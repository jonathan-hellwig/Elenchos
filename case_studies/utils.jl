using ModelingToolkit, OrdinaryDiffEq, Plots
function solve_ode(sys, u₀, tspan, p)
    prob = ODEProblem(sys, u₀, tspan, p)
    sol = solve(prob, Tsit5(), saveat = 0.01)
    return sol
end

function plot_solution(samples, solutions, color=:blue)
    plot(legend=false)
    for sol in solutions
        plot!(sol, vars=(1,2), linecolor=color, lw=1, alpha=0.5)
    end
    for sample in eachcol(samples)
        scatter!([sample[1]], [sample[2]], color=color, alpha=0.5)
    end
    display(plot!())
end

function plot_solution!(samples, solutions, color=:blue)
    for sol in solutions
        plot!(sol, vars=(1,2), linecolor=color, lw=1, alpha=0.5)
    end
    for sample in eachcol(samples)
        scatter!([sample[1]], [sample[2]], color=color, alpha=0.5)
    end
    display(plot!())
end
function plot_samples(samples, solutions, region, invariant)
    is_invariant = [all(invariant.(sol.u)) for sol in solutions]
    plot_solution(samples[:,is_invariant], solutions[is_invariant], :green)
    plot_solution!(samples[:,.!is_invariant], solutions[.!is_invariant], :red)
end

function sample_invariant(invariant, region, N)
    samples = rand(size(region,1), N) .* (region[:,2] - region[:,1]) .+ region[:,1]
    filter_indices = invariant.(eachcol(samples))
    return samples[:, filter_indices]
end