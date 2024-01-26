# TODO: Make the code runnable
# TODO: Add loops
# TODO: Add nondeterministic assignments

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

using Elenchos

@elenchos function max(x::Real, y::Real)
    @assert 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
end

using Elenchos
# The splitting implementation is equivalent to a cut in KeYmaera X
@elenchos function max(x::Real, y::Real)
    @assert 0 <= x
    if x >= y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x && max_value >= y
    max_value = max_value + 1
    @assert max_value >= x && max_value >= y
end

@elenchos function simulate()
    @assert 0 <= x && x <= y
    u = x_y_max
    @assert u == y
    @assert u >= x && u >= y
end

"""
Next features: 
- implement for and while loops
- implement communication with KeYmaera X server
- add better error messages for julia expression parsing
- develop a custom tactic for KeYmaera X to do the branch predicition
"""

@elenchos function simulate(T::Unsigned)
    @assert x >= 0 
    for _ in 1:T
        x = x + 1
    end
    @assert x >= 0
end

@elenchos function simulate(T::Unsigned)
    @assert x >= 0 && x * x >= 0
    for _ in 1:T
        @assert x >= 0
        x = x + 1

    end
    @assert x >= 0
end

@elenchos function simulate(T::Unsigned)
    @assert x >= 0 
    t = 0
    while t < T
        x = x + 1
        t = t + 1
    end
    @assert x >= 0
end

for _ in 1:2
    @assert x >= 0
    x = x + 1
    @assert x >= 0
end

@assert x >= 0
x = x + 1
@assert x >= 0
@assert x >= 0
x = x + 1
@assert x >= 0

for _ in 1:2
    @assert x >= 0
    x = x + 1
end

@assert x >= 0
x = x + 1
@assert x >= 0
x = x + 1

for _ in 1:2
    # Do invariants have a meaning outside of loops?
    @invariant x >= 0
    # @assert x >= 0
    x = x + 1
end
# {x:=x+1;}*@invariant(x>=0)

"""
Rright now, the deamon test does not split the program into two programs like I would want to do it.
There are several ways to implement splitting by assertions
1. Split the program into two subprograms and send them to KeYmaera X -> Trust my code to do the splitting correctly, feedback on the intermediate results
2. Send the whole program to KeYmaera X and provide a the cut tactic at the appropriate positions -> Get a witness for the whole program, no feedback on the intermediate results

Implementing the first approach allows me to avoid of working with the KeYmaera X codebase.

If I continue to follow this approach, I would need to also implement the loop invariant tactic in Julia.
"""

x = 0
begin
    x = x + 1
end

"""
    I need some kind of architecture too keep track of the goal graph.
    In the end, I want to be able to generate a witness for the whole program,
    but I also want to be able to generate a witness for each subprogram to have good user feedback.
    I want to be able to cache the results of the subprograms, so that I do not have to recompute them.
"""


"""
@elenchos function simulate(T::Unsigned)
    @invariant x >= 0 
    for _ in 1:T
        x = x + 1
    end
    @assert x >= 0
end

ProofGoal([ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :(x = x + 1))], [ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :())])

@elenchos function simulate(T::Unsigned)
    @invariant x >= 0 
    for _ in 1:T
        x = x + 1
        @assert x >= 1
        x = x + 1
    end
    @assert x >= 0
end

Should I just always translate for _ in 1:T to while true?

ProofGoalNode([ProofGoalNode([ProofGoalLeaf([:(x >= 0)], [:(x >= 1)], :(x = x + 1)), ProofGoalLeaf([:(x >= 1)], [:(x >= 0)], :(x = x + 1))]), ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :())])

@elenchos function simulate(T::Unsigned)
    t = 0
    @invariant x >= 0
    while t < T
        t = t + 1
        x = x + 1
        @assert x >= 1
        x = x + 1
    end
    @assert x >= 0
end


"""

"""
for t in 1:10
end

is not the same as

t = 1
while t <= 10
    t = t + 1
end

What if loops are not used to iterate over a time range?

for x in [1,2,3]
end

This should not be allowed!
function sum(x::Real, y::Real)
    result = 0
    for s in [x, y]
        result = s + 1
    end
end

I will only support loops of the form:

for _ in 1:T
end

and translate them to:
{}*
"""

"""

What happens in the following case:

@elenchos function simulate(T::Unsigned)
    @assert x >= 0
    x = x + 1
    for _ in 1:T
        x = x + 1
        @assert x >= 0
    end
    @assert x >= 0
end

I.e. when there is an assertion in the loop body, but no loop invariant?
Only support assertion in loop body if there is a loop invariant?

"""

# """
# @invariant x > 0 for _ in 1:10
#     x = x + 1
# end

# @invariant x > 0

# @invariant x > 0 x = sum(x, y)

# @invariant x > 0 begin
#     x = x + 1
#     x = x * x
# end
# """
using Elenchos
@elenchos function max(x::Real, y::Real)
    @assert x > 0
    if x > y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x
using Elenchos
@elenchos function simulate(x::Real)
    @assert x > 0
    while x < 10
    x = x + 1
    end
    @assert x > 0
end