using ModelingToolkit, OrdinaryDiffEq, Plots
function UnitMassWithFriction(k; name)
    @variables t x(t)=0 v(t)=0
    D = Differential(t)
    eqs = [D(x) ~ v
        D(v) ~ sin(t)]
    ODESystem(eqs, t; continuous_events = [v ~ 0], name) # when v = 0 there is a discontinuity
end
@named m = UnitMassWithFriction(0.7)
prob = ODEProblem(m, Pair[], (0, 10pi))
sol = solve(prob, Tsit5())
plot(sol)

@variables t x(t)=1 v(t)=0
D = Differential(t)

root_eqs = [x ~ 0]  # the event happens at the ground x(t) = 0
affect = [v ~ -v] # the effect is that the velocity changes sign

@named ball = ODESystem([D(x) ~ v
        D(v) ~ -9.8], t; continuous_events = root_eqs => affect) # equation => affect

ball = structural_simplify(ball)

tspan = (0.0, 5.0)
prob = ODEProblem(ball, Pair[], tspan)
sol = solve(prob, Tsit5())
@assert 0 <= minimum(sol[x]) <= 1e-10 # the ball never went through the floor but got very close
plot(sol)
minimum(sol[v])
maximum(sol[v])

sol[x]
# In dL: [(?x=0;v:=-v;{x'=v, v'=-g})*]
# More generally: [(⋃?Q;u:=u_i(x);{x'=f(x,u)})*]
function Ball(x0, v0; name)
    @variables t x(t)=x0 v(t)=v0
    D = Differential(t)
    root_eqs = [x ~ 0]
    affect = [v ~ -v]
    return ODESystem([D(x) ~ v, D(v) ~ -9.8], t; continuous_events = root_eqs => affect, name)
end

function Ball()
    @variables t x(t) v(t)

    function discrete(x,v)
        if x == 0
            v = -v
        end
        return [x,v]
    end
    return HybridSystem([D(x) ~ v, D(v) ~ -9.8], discrete, name)
end

function Ball()
    @variables t x(t) v(t)
    function system(x,v)
        if x == 0
            v = -v
        end
        @ode([D(x) ~ v, D(v) ~ -9.8], x >= 0)
    end
    return HybridSystem(system, name)
end

# General example for the case where I modify the way the system is defined
function General()
    @variables t x(t)
    @elenchos function system(x, t)
        @invariant invariant(x)
        u = controller(x)
        @assert property(x, u)
        @ode([D(x) ~ f(x,u)], Q(x, t))
    end
    return HybridSystem(system, name)
end

# Which is equivalent to
function General()
    @variables t x(t)
    affect = [u ~ controller(x)]
    roots_eqs = [!Q(x,t)] # Check if other types of events other than equality are possible
    return ODESystem([D(x) ~ f(x,u)], t; continuous_event = root_eqs => affect, name)
end
sol = solve(ODEProblem(General(), Pair[], (0, 10pi)), Tsit5())
result = solve(SymbolicProblem(General(), Pair[], safety_property), KeYmaeraX())

# Second design
# General example for the case where I modify the way the system is defined
function General()
    @variables t x(t)
    # I do not need to define the system as a function
    @elenchos System begin
        @invariant invariant(x)
        u = controller(x)
        @assert property(x, u)
        # Similar to JuliaReach
        @IVP([D(x) ~ f(x,u)], Q_1(x, t), Q_2(x, t))
    end
    return HybridSystem(System, name)
end

# One way
function discrete(x,v)
    if x == 0
        v = -v
    end
    return [x,v]
end

function continuous(x,v)
    return [v, -9.8]
end

function Ball()
    return ODESystem(continuous, discrete)
end

# One example, where you literally just use the simulation code
# What do I do about differential ghost and differential cuts?

"""
This design decouples the trigger condition from the effect of the event.

One issue I see with this design is that the ODE in the last line of the system definition is required for the whole systems to work correctly.

I feel like this approach would only work if I had strong automation on the KeYmaeraX side to generate differential invariants. This could be a research project in itself. How do I generate the correct differential invariant, cuts and ghost automatically?
"""
function Thermostat(x0, a; name)
    @variables t x(t)=x0 u a
    # I do not need to define the system as a function
    @hybrid system begin
        @invariant x >= 0
        if x == 19
            u = 0
        elseif x == 21
            u = 30
        end
        @ode(x' = -a * (x - u), x <= 19, 19 <= x <= 21, 21 <= x <= 22)
    end
    return HybridSystem(system, t, name)
end

# The same system with ModelingToolkit
# This design feels cleaner, but it is not clear where to put annotations such as invariants and assertions
function Thermostat(x0, a; name)
    @variables t x(t) u a
    D = Differential(t)
    continuous_events = [[x ~ 19] => [u ~ 0], [x ~ 21] => [u ~ 30]]
    eqs = [D(x) ~ -a * (x - u)]
    ODESystem(eqs, t; continuous_events, name)
end

# In the standard version of DifferentialEquations.jl, events are not part of the system definition and are passed as an argument to the solve function. They are allowed to directly interact with the integrator of the solve function. I think my design should be more similiar to the approach of ModelingToolkit.jl. This design is most appropriate for the cases where you are modelling hierarchical systems, where events are specific to a subsystem and not the whole system.