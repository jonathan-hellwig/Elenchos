using ModelingToolkit, OrdinaryDiffEq, Plots

v_h = 50.0
@parameters a b
@variables t v(t) u(t)
@variables x(t) [output = true]
D = Differential(t)
continuous_events = [[x ~ 19] => [v ~ v_h], [x ~ 21] => [v ~ 0]]
eqs = [D(x) ~ -a * (x - u), D(u) ~ -b * (u - v), D(v) ~ 0.0]
@named thermostat = ODESystem(eqs, t; continuous_events)
thermostat = structural_simplify(thermostat)

tspan = (0.0, 10.0)
p = [a => 0.3, b => 0.9, v_h => 50]

function solve_ode(x0, u0, v0, p)
    prob = ODEProblem(thermostat, [x=>x0, u=>u0, v=>v0], tspan, p)
    sol = solve(prob, Tsit5())
    return sol
end

function plot_solutions(solutions, color=:blue)
    plot(legend=false)
    for sol in solutions
        plot!(sol, vars=(t,x), linecolor=color, lw=1, alpha=0.5)
    end
    display(plot!())
end

function plot_solutions!(solutions, color=:blue)
    for sol in solutions
        plot!(sol, vars=(t,x), linecolor=color, lw=1, alpha=0.5)
    end
    display(plot!())
end
p = [a => 0.2, b => 0.5, v_h => 50]
solutions = solve_ode(20.0, 0.0, 0.0, p)
plot_solutions(solutions)
plot_solutions!(solutions, :black)

# t = LinRange(pi, 2*pi, 15)
# x1 = 20 .+ 3 * sin.(t)
# x2 = 20 .+ 20 * cos.(t)

# solutions = solve_ode.(x1, x2)
# plot_solutions(solutions)

# t = LinRange(0, 2* pi, 100)
# x1 = 20 .+ 3 * sin.(t)
# x2 = 20 .+ 20 * cos.(t)
# plot!(x1, x2, label="Ellipse", lw=1, color=:black, alpha=0.5)

function draw_ellipse!()
    t = LinRange(0, 2* pi, 100)
    x1 = 20 .+ 3 * sin.(t)
    x2 = 20 .+ 20 * cos.(t)
    display(plot!(x1, x2, label="Ellipse", lw=1, color=:black, alpha=0.5))
end
# Sample initial condition for the ellipse with rejection sampling
# function sample_uniformly_from_ellipse(xc, yc, a, b, θ, N)
#     φ = rand(N) * 2π # Uniformly sample the angle φ
#     r = sqrt.(rand(N)) # Uniformly sample the scaled radius for uniform area distribution
#     x_samples = xc .+ (a .* r) .* cos.(φ) .* cos(θ) - (b .* r) .* sin.(φ) .* sin(θ)
#     y_samples = yc .+ (a .* r) .* cos.(φ) .* sin(θ) + (b .* r) .* sin.(φ) .* cos(θ)
#     return x_samples, y_samples
# end

# # Define the parameters for the ellipse
# xc = 20.0 # x-coordinate of the center
# yc = 20.0 # y-coordinate of the center
# a1 = 3.0 # Semi-major axis
# b1 = 20.0 # Semi-minor axis
# θ = 0.0 # Rotation angle in radians
# N = 100 # Number of samples

# # Sample from the ellipse
# x_samples, y_samples = sample_uniformly_from_ellipse(xc, yc, a1, b1, θ, N)
# filter_indices = x_samples .<= 19.0
# x_samples = x_samples[filter_indices]
# y_samples = y_samples[filter_indices]
# solutions = solve_ode.(x_samples, y_samples)
# plot_solutions(solutions)


"""
TODO: 
- [x] sample from invariant candiate
- [x] fix the modeling issue
- [x] simulate systems with sampled initial conditions
- [x] detect invariant violations
- [x] plot trajectories in the state space, the invariant, and the invariant violations
- [ ] scatter plot of the points where the gradient of the invariant is increasing
"""

# Sample from the invariant candidate via rejection sampling
# invariant(x) = (x[1] - 20)^2 / 3^2 + (x[2] - 20)^2 / 20^2 - 1 <= 0
invariant(x) = (x[1] >= 1/200* (x[2] - 20)^2 + 17) && (x[2] >=0)
function sample_invariant(invariant, region, N)
    samples = rand(size(region,1), N) .* (region[:,2] - region[:,1]) .+ region[:,1]
    filter_indices = invariant.(eachcol(samples))
    return samples[:, filter_indices]
end

# region = [17.0 23.0; 0.0 40.0]
region = [17.0 23.0; 0.0 40.0]
samples = sample_invariant(invariant, region, 400)
# scatter(samples[1,:], samples[2,:], label="Samples", color=:black, markersize=1, legend=false)
# TODO: do not forget to adjust v_h
v0 = ifelse.(samples[1,:] .< 19.0, 50.0, 0.0)
solutions = solve_ode.(samples[1,:], samples[2,:], v0)

non_violations = [all(invariant.(sol.u)) for sol in solutions]
non_violating_solutions = solutions[non_violations]
violating_solutions = solutions[.!non_violations]
plot_solutions(violating_solutions, :red)
plot_solutions!(non_violating_solutions, :green)
scatter!(samples[1,non_violations], samples[2,non_violations], label="Violating samples", color=:green, markersize=3, legend=false)
scatter!(samples[1, .!non_violations], samples[2, .!non_violations], label="Non-violating samples", color=:red, markersize=3, legend=false)
# draw_ellipse!()
u_values = 0:0.1:40
x_values = 1/200 * (u_values .- 20).^2 .+ 17
plot!(x_values, u_values, label="Invariant", color=:black, lw=2, alpha=0.5)
y = 19:0.1:24
plot!(y,0.0 .* y, label="Initial condition", color=:black, lw=2, alpha=0.5)
plot!(y,0.0 .* y .+ 40.0, label="Initial condition", color=:black, lw=2, alpha=0.5)


