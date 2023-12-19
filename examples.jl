# I do not want to stop execution when an assertion fails. 
# I just want to return a simulation trace for visualization purposes.
macro assume(e, trace...)
    trace = isempty(trace) ? :([]) : esc(:($trace))
    return quote
        if !$(e)
            return $trace
        end
    end
end

macro invariant(e, trace...)
    trace = isempty(trace) ? :([]) : esc(:($trace))
    return quote
        if !$(e)
            return $trace
        end
    end
end

"""
    RealFunction

A real function is a function from reals to reals, f : `Real` x `Real` x ... x `Real` -> `Real`.
"""
struct RealFunction{F <: Function}
    f::F
end

"""
    Formula
    A formula is a function from reals to booleans, P : `Real` x `Real` x ... x `Real` -> `Bool`
"""
struct Formula{F <: Function}
    P::F
end

function nondeterministic_assignment(x::Real, f::RealFunction)
    @assume 0 <= x <= 1
    x = f(x)
    @assert 0 <= x <= 1
end

function nondeterministic_choice(x::Real, P::Formula)
    @assume 0 <= x <= 1
    if P(x)
        x = 0.0
    else
        x = 1.0
    end
    @assert 0 <= x <= 1
end

function nondeterministic_loop(x::Real, T::Integer)
    @assume 0 <= x <= 1 && T > 0
    for _ in 1:T
        @invariant 0 <= x <= 1
            x = 1.0
    end
    @assert 0 <= x <= 1
end

"""
Forward driving car example
Corresponding to:

v>=0 & A>0 & B>0                     
->                                     
[                                      
  {                                    
    {?v<=5;a:=A; ++ a :=0; ++ a:=-B; } 
    {x'=v , v'=a & v>=0}               
  }*@invariant(v>=0)                   
] v>=0

Open questions:
1. How do I handle multiple nondeterministic choice branches?
2. How do I handle break conditions?
3. How do I handle return values?

"""
function forward_driving_car(x::Real, v::Real, A::Real, B::Real, T₁::Integer, T₂::Integer, P::Formula)
    @assume  v >= 0 && 0 < A && 0 < B && T₁ > 0 && T₂ > 0
    for _ in 1:T₁
        @invariant 0 <= v
        # Control law
        if v <= 5
            a = A
        elseif P()
            a = 0
        else
            a = -B
        end

        for _ in 1:T₂
            x_new, v_new = x + v, v + a
            if v_new >= 0
                x, v = x_new, v_new
            end
        end
        #= Or equivalently:
        for _ in 1:T₂
            if v + a >= 0
                continue
            else
                x, v = x+v, v+a
            end
        end
        =#
        # For simulation purposes, the break condition is necessary. 
        # {x_new = x + v; v_new = v + a; ? v_new >= 0; x := x_new; v := v_new;}*
        # {? v + a < 0; x := x + v; v := v+a;}*

    end
    @assert 0 <= v
    return trace
end

"""
    Linear system example
This example shows an important pattern for nondeterministism. The code 
    ```
    u = control_law(x, a, b)
    @assert 0 <= u <= 1
    ```
allows the user to specify a control law that statisfies the bounds on u.
"""
function linear_system(x::Real, a::Real, b::Real, T₁::Integer, T₂::Integer, control_law::RealFunction)
    @assume 0 <= x && T₁ > 0 && T₂ > 0
    for _ in 1:T₁
        @invariant 0 <= x
        u = control_law(x, a, b)
        @assert 0 <= u <= 1
        #= 
        Could also be modelled by the following code:
        ```
        u = control_law(x, a, b)
        if ! (0 <= u <= 1)
            continue
        end
        ```
        Which is equivalent to `u = *;? 0 <= u & 0 <= 1;`
        =#
        for _ in 1:T₂
            x = a * x + b * u
        end
    end
    @assert 0 <= x
end

"""
    State triggered event example
This is not optimal for simulation purposes, because the loop might continue to run even though nothing changes.

The loop block is equivalent to the formula {?x<10;x:=x+1 ++ ?x>=10;}*
"""
function state_triggered(x::Real, T::Interger)
    @assume 0 == x && T > 0
    for _ in 1:T
        @invariant 0 <= x <= 9
        if x < 10
            x = x + 1
        end
    end
    @assert 0 <= x <= 9
end

"""
    Time triggered event example
"""
function time_triggered(x::Real, T::Interger)
    @assume 0 == x && T > 0
    # This approach might cause issues, because even though we have 0 <= x <= 9, the loop might continue to run and time might increase to T.
    for t in 1:T
        @invariant 0 <= x <= 9
        if t <= 10
            x = x + 1
        end
    end
    @assert 0 <= x <= 9
end

"""
    System trace example
If assertions fail, the a trace of the system is returned.

Two questions:
1. How do I allow the user to have some flexibility in the return value?
    - Return a trace if assertions fail, otherwise return an empty list. Disallow the user from using the trace in the program.
    - Instead of returning from the function when an assertion fails, allow the user to record the trace and continue execution.
"""
# First approach
function system_trace(x::Real, T::Integer)
    trace = []
    @assume  0 <= x && T > 0 trace
    for _ in 1:T
        @invariant 0 <= x trace
        x = x + 1.0
        push!(trace, x)
    end
    @assert 0 <= x
    return trace
end

# Second approach
struct Trace
    trace::Vector{Float64}
end

function system_trace(x::Real, T::Integer, trace::Trace)
    @assume  0 <= x && T > 0 trace
    for _ in 1:T
        @invariant 0 <= x trace
        x = x + 1.0
        push!(trace, x)
    end
    return trace
end


"""
    Allowed operations
"""
function allowed_operations(x::Real, T::Integer)
   println("Allowed operations:$x")
end

"""
    Composition of systems
"""
function control_law(x::Real, a::Real, b::Real)
    @assume 0 <= x && 0 < a && 0 < b
    if x <= 5 && a <= 1
        u = a
    elseif x <= 5 && b <= 1
        u = b
    else
        u = 0.5
    end
    @assert 0 <= u <= 1
    return u
end

function control_system(x::Real, a::Real, b::Real, T::Integer)
    @assume 0 <= x && T > 0 && a > 0 && b > 0
    for _ in 1:T
        @invariant 0 <= x
        # Preconditions of control_law have to be satisfied
        u = control_law(x, a, b)
        x = a * x + b * u
    end
    @assert 0 <= x
end

# Example code
@trace function max(x::Real, y::Real)
    @assume 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
    return max_value
end

using MacroTools, Test


macro trace(ex)
    # TODO: Use the functions below to parse the expression into a dL_IR
    argument_variables = parse_arguments(ex)
    body_variables, program, assumptions, assertions = parse_body(ex)
    variables = union(argument_variables, body_variables)
    return dL_IR(variables, program, assumptions, assertions)
end

function parse_body()
    assertions = collect_assertions(ex)
    assumptions = collect_assumptions(ex)
    variables = collect_unique_variables(ex)

    program = remove_assertions(ex)
    program = remove_assumptions(program)

    return variables, program, assumptions, assertions
end


function collect_assumptions()
    #TODO: Collect all assumptions in the program
end

function remove_assertions()
    # TODO: Remove assertions from the program
end

function remove_assumptions()
    #TODO: Remove assumptions from the program
end

function collect_variables()
    #TODO: Collect all variables in the program

end

struct dL_IR
    variables::Vector{Tuple{Symbol, Type}}
    program::Expr
    assumptions::Vector{Expr}
    assertions::Vector{Expr}
end

@enum Type Real Integer Boolean

function parse_arguments(ex)
    #TODO: Check whether this is robust
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))

    variables = Set{Tuple{Symbol, Symbol}}()
    println(xs)
    for x in xs
        @capture(x, y_::t_)
        push!(variables, (y, t))
    end
    return variables
end

ex = quote
    function max(x::Real, y::Real)
        @assume 0 <= x && 0 <= y
        if x >= y
            max_value = x
        else
            max_value = y
        end
        
        @assert max_value >= x && max_value >= y
        @assert max_value == x || max_value == y
        return max_value
    end
end
@test parse_arguments(ex) == Set{Tuple{Symbol, Symbol}}([(:x, :Real), (:y, :Real)])


function collect_assertions(ex)
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    assertions = Vector{Expr}()
    for x in body.args
        println(x)
        if isa(x, Expr) && @capture(x, @assert q_)
            push!(assertions, q)
        end
    end
    return assertions
end
@test collect_assertions(ex) == [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]

