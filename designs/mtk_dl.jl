using ModelingToolkit
using Plots
using DifferentialEquations
using ModelingToolkit: t_nounits as t, D_nounits as D
using HTTP
@mtkmodel Heater begin
    @variables begin
        x(t)
        # u(t)
    end
    @equations begin
        D(x) ~ -x
        # D(u) ~ -u + 1
    end
end

@mtkbuild heater = Heater()
prob = ODEProblem(heater, [heater.x => 0.6], (0.0, 10.0))
sol = solve(prob)
plot!(sol, vars=(t, heater.x), label="x")
# plot!(sol, vars=(t, heater.u), label="x")
plot(sol, vars=(heater.u, heater.x), label="phase plot")
problem = SymbolicProblem(heater, (heater.x > 0), (heater.x > 0))
prove(problem)

eq = equations(heater)
eq[1]

# build_function(heater, :heater, sys=ODESystem, expression=false)
# heater(0.0, [0.0, 0.0])
eq[1]
using Symbolics
expr = toexpr(eq[1])
expr.args[3].args
function system_to_dl(sys)
    eqs = toexpr(equations(sys))
    result = ""
    for eq in eqs[1:end-1]
        result = result * ode_to_dl(eq) *","
    end
    result = result * ode_to_dl(eqs[end])
    return result
end

function ode_to_dl(expr)
    @assert length(expr.args) == 3
    dx = expr.args[2].args[2]
    rhs = expr.args[3]
    # if rhs.
    return term_to_string(dx) * "' = " * term_to_string(rhs)

end

function term_to_string(term)
    if term isa Number
        return string(term)
    elseif term isa Symbol
        return string(term)
    elseif term isa Expr && term.head == :call && length(term.args) == 2
        # println(term)
        return term_to_string(term.args[1])
    elseif term isa Expr && term.head == :call && length(term.args) == 3
        return "(" * term_to_string(term.args[2])* String(Symbol(term.args[1])) * term_to_string(term.args[3]) * ")"
    else
        error("Unknown term type: $term")
    end
end

system_to_dl(heater)

assumptions = (heater.u >= 0) & (heater.u <= 1)
term(assumptions)
term_to_string(toexpr(assumptions))
as = toexpr(assumptions)

function SymbolicProblem(sys, preconditions, postconditions)
    return Dict("sys" => sys, "pre" => preconditions, "post" => postconditions)
end

function parse_response(response)
    if isnothing(response)
        return nothing
    end
    body = String(response.body)
    if contains(body, "PROVED")
        return true
    elseif contains(body, "UNFINISHED") || contains(body, "FAILED")
        return false
    else
        return nothing
    end
end

function prove(problem::Dict, invariant=nothing)
    sys = problem["sys"]
    pre = problem["pre"]
    post = problem["post"]
    # invariant_str = term_to_string(toexpr(invariant))
    sys_str = system_to_dl(sys)
    pre_str = term_to_string(toexpr(pre))
    post_str = term_to_string(toexpr(post))
    name = hash(problem)
    # println("Proving that $pre_str -> [{$sys_str}@invariant($invariant_str)] $post_str")
    if isnothing(invariant)
        invariant_str = ""
    else
        invariant_str = "@invariant(" * term_to_string(toexpr(invariant)) * ")"
    end
    kyx_string = "Theorem \"$name.kyx\"\n" *
                    "   ProgramVariables\n" *
                    # "       Real u;" * "\n" *
                    "       Real x;" * "\n" *
                    "   End.\n" *
                    "   Problem\n" *
                    "      $pre_str -> [{$sys_str}$invariant_str] $post_str\n" *
                    "   End.\n" *
                    "   Tactic\n" *
                    "      auto\n" *
                    "   End.\n" *
                    "End."
    println(kyx_string)
    response = nothing
    is_success = true
    response = HTTP.post("http://localhost:8070/check", Dict("Content-Type" => "text/plain"), kyx_string)
    try
        response = HTTP.post("http://localhost:8070/check", Dict("Content-Type" => "text/plain"), kyx_string)
    catch
        println("Failed to send proof request")
        is_success = false
    end
    is_success = parse_response(response)
    if isnothing(is_success)
        println("Unexpected error")
        return
    end
    if is_success
        println("Proved")
    else
        println("Failed to prove")
    end
end

# problem = SymbolicProblem(heater, (heater.x > 0), (heater.x > 0))
prove(problem, heater.x >= 0)

