using ModelingToolkit, Plots, DifferentialEquations
using ModelingToolkit: t_nounits as t, D_nounits as D

@connector Pin begin
    v(t)
    i(t), [connect = Flow]
end

@mtkmodel Ground begin
    @components begin
        g = Pin()
    end
    @equations begin
        g.v ~ 0
    end
end

@mtkmodel OnePort begin
    @components begin
        p = Pin()
        n = Pin()
    end
    @variables begin
        v(t)
        i(t)
    end
    @equations begin
        v ~ p.v - n.v
        0 ~ p.i + n.i
        i ~ p.i
    end
end

@mtkmodel Resistor begin
    @extend OnePort()
    @parameters begin
        R = 1.0 # Sets the default resistance
    end
    @equations begin
        v ~ i * R
    end
end

@mtkmodel Capacitor begin
    # No explicit list of inputs and outputs
    @extend OnePort()
    @parameters begin
        C = 1.0
    end
    @equations begin
        D(v) ~ i / C
    end
end

@mtkmodel ConstantVoltage begin
    @extend OnePort()
    @parameters begin
        V = 1.0
    end
    @equations begin
        # V ~ v
        V ~ Sample(t, 0.1)(v)
    end
end

@mtkmodel RCModel begin
    # @parameters begin
    #   R
    #   C
    #   V
    # end
    @components begin
        resistor = Resistor(R = 1.0)
        # all other components do not involve an ODE
        # @assert capacitor.v <= 1
        capacitor = Capacitor(C = 1.0)
        source = ConstantVoltage(V = 1.0)
        ground = Ground()
    end
    @equations begin
        # Depending on the type of connector used, the equation can be different
        connect(source.p, resistor.p)
        connect(resistor.n, capacitor.p)
        connect(capacitor.n, source.n)
        connect(capacitor.n, ground.g)
    end
    # @requires begin
    #    0 <= R <= 1
    #    0 <= C <= 1
    #    0 <= V <= 1
    # end
    # @invariant begin
    #  TODO
    # end
    # @ensures begin
    #   capacitor.v <= 1
    # end
end 

# This steps reduces the model 
@mtkbuild rc_model = RCModel(resistor.R = 2.0)
u0 = [
    rc_model.capacitor.v => 0.0
]
prob = ODEProblem(rc_model, u0, (0, 10.0))
sol = solve(prob)
plot(sol)

equations(rc_model)
full_equations(rc_model)
parameters(rc_model)

function UnitMassWithFriction(k; name)
    @variables x(t)=0 v(t)=0
    eqs = [D(x) ~ v
           D(v) ~ sin(t) - k * sign(v)]
    ODESystem(eqs, t; continuous_events = [v ~ 0], name) # when v = 0 there is a discontinuity
end
@mtkbuild m = UnitMassWithFriction(0.7)
full_equations(m)
structural_simplify(m)
prob = ODEProblem(structural_simplify(m), Pair[], (0, 10pi))
sol = solve(prob, Tsit5())
plot(sol)


dt = 0.1
@variables x(t) y(t) u(t) yd(t) ud(t) r(t)
@parameters kp
# u(n + 1) := f(u(n))

eqs = [yd ~ Sample(t, dt)(y)
       ud ~ kp * (r - yd)
       r ~ 1.0

       # plant (time continuous part)
       u ~ Hold(ud)
       D(x) ~ -x + u
       y ~ x]
@named sys = ODESystem(eqs, t)
ss = structural_simplify(sys);

Tf = 1.0
prob = ODEProblem(ss, [x => 0.0, y => 0.0], (0.0, Tf), [kp => 1.0])
sol = solve(prob)


@info "Testing shift normalization"
dt = 0.1
@variables x(t) y(t) u(t) yd(t) ud(t) r(t) z(t)
@parameters kp
d = Clock(t, dt)
k = ShiftIndex(d)

eqs = [yd ~ Sample(t, dt)(y)
       ud ~ kp * (r - yd) + z(k)
       r ~ 1.0
       # plant (time continuous part)
       u ~ Hold(ud)
       D(x) ~ -x + u
       y ~ x
       z(k + 2) ~ z(k) + yd
       ]
@named sys = ODESystem(eqs, t)
ss = structural_simplify(sys);

Tf = 1.0
prob = ODEProblem(ss, [x => 0.0, y => 0.0], (0.0, Tf),
    [kp => 1.0; z => 3.0; z(k + 1) => 2.0])
sol = solve(prob, Tsit5(), kwargshandle = KeywordArgSilent)
plot(sol)