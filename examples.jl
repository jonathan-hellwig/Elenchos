# I do not want to stop execution when an assertion fails. 
# I just want to return a simulation trace for visualization purposes.
macro assume(e)
    return :(@assert $(esc(e)) "Assumption violated: $e")
end

macro invariant(e)
    return :(@assert $(esc(e)))
end

struct RealFunction
    # A real function is a function from reals to reals, f : R -> R
    f::Function
end

struct Formula
    # A formula is a function from reals to booleans, P : R -> Bool
    P::Function
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
                break # In dL this is continue
            else
                x, v = x_new, v_new
            end
        end
        #= Or equivalently:
        for _ in 1:T₂
            if v + a >= 0
                break
            else
                x, v = x+v, v+a
            end
        end
        =#
        # For simulation purposes, the break condition is necessary. 
        # However, the behavior of the dL models below correponds to continue instead of break.
        # {x_new = x + v; v_new = v + a; ? v_new >= 0; x := x_new; v := v_new;}*
        # {? v + a < 0; x := x + v; v := v+a;}*

    end
    @assert 0 <= v
end
