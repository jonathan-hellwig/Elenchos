using ModelingToolkit, OrdinaryDiffEq, Plots

function Thermostat(; name)
    # v_h = 50.0
    # The parameter does not ret registered in the model if it is not used in the equations
    # @parameters a b v_h
    pars = @parameters begin
        a
        b
        v_h
        x_low
        x_high
    end
    @variables t
    vars = @variables begin
        x(t)
        u(t)
        v(t)
    end
    D = Differential(t)
    continuous_events = [[x ~ x_low] => [v ~ v_h], [x ~ x_high] => [v ~ 0]]
    eqs = [D(x) ~ -a * (x - u), D(u) ~ -b * (u - v), D(v) ~ 0.0]
    return ODESystem(eqs, t, vars, pars; continuous_events, name)
end

function solve_ode(x0, u0, p)
    tspan = (0.0, 10.0)
    x_high = Dict(p)[thermostat.x_high]
    v_h = Dict(p)[thermostat.v_h]
    v0 = ifelse(x0 < x_high, v_h, 0.0)
    prob = ODEProblem(thermostat, [thermostat.x=>x0, thermostat.u=>u0, thermostat.v=>v0], tspan, p)
    sol = solve(prob, Tsit5(), saveat = 0.01)
    return sol
end

function plot_solutions(solutions, color=:blue)
    plot(legend=false)
    for sol in solutions
        plot!(sol, vars=(1,2), linecolor=color, lw=1, alpha=0.5)
    end
    display(plot!())
end

function plot_solutions!(solutions, color=:blue)
    for sol in solutions
        plot!(sol, vars=(1,2), linecolor=color, lw=1, alpha=0.5)
    end
    display(plot!())
end
function draw_ellipse!()
    t = LinRange(0, 2* pi, 100)
    x1 = 20 .+ 3 * sin.(t)
    x2 = 20 .+ 20 * cos.(t)
    display(plot!(x1, x2, label="Ellipse", lw=1, color=:black, alpha=0.5))
end

function sample_invariant(invariant, region, N)
    samples = rand(size(region,1), N) .* (region[:,2] - region[:,1]) .+ region[:,1]
    filter_indices = invariant.(eachcol(samples))
    return samples[:, filter_indices]
end

@named thermostat = Thermostat()
thermostat = structural_simplify(thermostat)

p = [thermostat.a => 0.3, thermostat.b => 0.9, thermostat.v_h => 40, thermostat.x_low => 19, thermostat.x_high => 21]
sol = solve_ode(20, 0, p)

# invariant(x) = (x[1] - 20)^2 / 3^2 + (x[2] - 20)^2 / 20^2 - 1 <= 0
invariant(x) = (x[1] >= 1/200* (x[2] - 20)^2 + 17) && (x[2] >=0) && (x[2] <= 40) && x[1] <= -1/200* (x[2] - 20)^2 + 23
# region = [17.0 23.0; 0.0 40.0]
region = [17.0 23.0; 0.0 40.0]
samples = sample_invariant(invariant, region, 100)
solutions = solve_ode.(samples[1,:], samples[2,:], Ref(p));

non_violations = [all(invariant.(sol.u)) for sol in solutions]
non_violating_solutions = solutions[non_violations];
violating_solutions = solutions[.!non_violations];
plot_solutions(non_violating_solutions, :green)
plot_solutions!(violating_solutions, :red)
scatter!(samples[1,non_violations], samples[2,non_violations], label="Violating samples", color=:green, markersize=3, legend=false)
scatter!(samples[1, .!non_violations], samples[2, .!non_violations], label="Non-violating samples", color=:red, markersize=3, legend=false)
# draw_ellipse!()
u_values = 0:0.1:40
x_values = 1/200 * (u_values .- 20).^2 .+ 17
plot!(x_values, u_values, label="Invariant", color=:black, lw=2, alpha=0.5)

u_values = 0:0.1:40
x_values = -1/200 * (u_values .- 20).^2 .+ 23
plot!(x_values, u_values, label="Invariant", color=:black, lw=2, alpha=0.5)

y = 19:0.1:21
plot!(y,0.0 .* y, label="Initial condition", color=:black, lw=2, alpha=0.5)
plot!(y,0.0 .* y .+ 40.0, label="Initial condition", color=:black, lw=2, alpha=0.5)

p = [thermostat.a => 0.3, thermostat.b => 0.9, thermostat.v_h => 40, thermostat.x_low => 19, thermostat.x_high => 21]
sol = solve_ode(21, 40, p)
plot!(sol, vars=(1,2), linecolor=:blue, lw=2, alpha=0.5)
as = 0.5:0.1:4.0
x_vals = zeros(length(as))
u_vals = zeros(length(as))
plot(xlim=(7, 25), ylim=(0, 40), legend=false)
for i in length(as):length(as)
    p = [thermostat.a => as[i], thermostat.b => 0.9, thermostat.v_h => 40, thermostat.x_low => 19, thermostat.x_high => 21]
    sol = solve_ode(19, 0, p)
    u = hcat(sol.u...)
    _, index = findmin(u[1,:])
    x_vals[i] = u[1,index]
    u_vals[i] = u[2,index]
    # u_s, x_s = model5(as[i], fit.param)
    x_s = x_vals[i] -0.5
    u_s = u_vals[i]
    m_1 = (19 - x_s) / u_s^2
    x_values = m_1 * (u_values .- u_s).^2 .+ x_s
    display(scatter!([u[1,index]], [u[2,index]], label=false, color=:black, markersize=3))
    display(plot!(sol, vars=(1,2), label = false, linecolor=:blue, lw=2, alpha=0.5))
    display(plot!(x_values, u_values, label=false,lw=2, alpha=0.5, linecolor=:red))
end
# p = [thermostat.a => 0.3, thermostat.b => 0.9, thermostat.v_h => 40, thermostat.x_low => 19, thermostat.x_high => 21]
# sol = solve_ode(19, 0, p)
# plot!(legend = true)
for a in 0.5:0.5:3.0
    u_values = 0:0.1:40
    # x_values = 1/200 * (u_values .- 20).^2 .+ 17 .- 8 * a^(1/4)
    # x_values = 1/200 * (u_values .- value(c_2) * a).^2 .+ value(c_4).+ value(c_3) * a

display(plot!(x_values, u_values, label="a $a",lw=2, alpha=0.5))
end


# Optimization conditions
# I am looking for a function f(u)
# 1. f(0) = 19
# 2. min_t x(t) >= min_u f(u)
# 3. f(u(argmin_t x(t)) = min_u f(u)

# f(u, a) = c_1 * a * (u - c_2 * a)^2 + 17 - c_3 * exp(- c_4 * a)

using JuMP, Ipopt

model = Model(Ipopt.Optimizer)
set_silent(model)
# @variable(model, c_1, start = 1/200)
@variable(model, c_2)
@variable(model, c_3)
@variable(model, c_4)
# @constraint(model, c_4 >= 0)
# @constraint(model, c_1 >= 0)
# @constraint(model, c_2 >= 10)
# @constraint(model, [i in 1:length(as)], c_1 * as[i] * (c_2 * as[i])^2 + 17 - c_3 * as[i] == 19)
@objective(model, Min, sum((u_vals[i] - c_2 * as[i])^2 + (x_vals[i] - c_3 * as[i] + c_4)^2 for i in 1:length(as)))
optimize!(model)
solution_summary(model)
Test.@test is_solved_a
value(c_1)

# Plot the solution

plot()
for i in 1:length(as)
    u_values = 0:0.1:40
    x_values = value(c_1) * as[i] * (u_values .- value(c_2) * as[i]).^2 .+ 17 .- value(c_3) * as[i]
    display(plot!(x_values, u_values, label="a $as[i]",lw=2, alpha=0.5))
end
plot()
u_values = 0:0.1:40
x_values = value(c_1) * 0.5 * (u_values .- value(c_2) * 0.5).^2 .+ 17 .- value(c_3) * 0.5
display(plot!(x_values, u_values,lw=2, alpha=0.5))

y = 0.5:0.1:40
plot(y,log.(y), label="Initial condition", color=:black, lw=2, alpha=0.5)


# General from
# f(c_1, c_2, c_3, c_4) = (u + c_1 * log(a) + c_2)^2 + c_3 + c_4 * log(a)

model = Model(Ipopt.Optimizer)
set_silent(model)
@variable(model, c_1)
# @variable(model, c_2)
@variable(model, c_3)
@variable(model, c_4)

# @constraint(model, [i in 1:length(as)], c_1 * as[i] * (c_2 * as[i] + c_3 * log(as[i]) + c_3)^2 + c_3 + c_4 * log(as[i]) == 19)
@objective(model, Min, sum((1/200*(u_vals[i] + c_1 * log(as[i]) + 10)^2 + c_3 + c_4 * log(as[i]) - x_vals[i])^2 for i in 1:length(as)))
optimize!(model)
solution_summary(model)
plot()
for i in 1:4:length(as)
    u_values = 0:0.1:40
    x_values =1/200*(u_values .+ value(c_3) * log(as[i]) .+ 10).^2 .+ value(c_3) .+ value(c_4) * log(as[i])
    display(plot!(x_values, u_values, label=false,lw=2, alpha=0.5))
end

using LsqFit
# using Logging: global_logger
# using ConsoleLogger: ConsoleLogger
# global_logger(ConsoleLogger(stderr, Logging.Warn))
# Define the model: y = a1*log(x) + a2
# model(x, p) = p[1]*log.(x) .+ p[2]
model(x, p) = [p[1]*log.(x) .+ p[2]; p[3]*log.(x) .+ p[4]]
model2(x, p) = [p[1]*1.0 ./ (x .+ 5.0) .+ p[2]; p[1]*1 ./ (x .+ 5.0) .+ p[2]]
model3(x, p) = [p[1]*(x .- x.^2/2 + x.^3/3 - x.^4/4) .+ p[2]; p[3]*(x .- x.^2/2 + x.^3/3 - x.^4/4) .+ p[4]]
model(as, [0.0, 0.0, 1.0, 1.0])
model5(x, p) = [p[1]*x .+ p[2]; p[3]*x .+ p[4]]

# Initial guess for the parameters [a1, a2]
p0 = [2.0, 1.0, 2.0, 1.0]

# Fit the model to the data
combined_data = vcat(x_vals, u_vals)
fit = curve_fit(model5, as, combined_data, p0)

# Extract the fitted parameters
a1, a2, a3, a4 = fit.param
estimate_covar(fit)

println("Fitted parameters:")
println("a1 = $a1")
println("a2 = $a2")
prediction = model5(as, fit.param)
mid = length(prediction)÷2
x_pred = prediction[1:mid]
u_pred = prediction[mid+1:end]
# Plot the data and the fitted model
scatter(x_vals, u_vals, label="Data", lw=2, color=:black, legend=:topleft)
scatter!(x_pred, u_pred, label="Fitted model", lw=2, color=:red)

t = 0.1:0.1:4
plot(t, log.(t))
plot!(t, -1 ./ t)


# Parabola model: x = m * (u - u_s)^2 + x_s
# x(0) = 19 <-> 19 = m * u_s^2 + x_s <-> m = (19 - x_s) / u_s^2
# x(p) = q <-> q = m * (p - u_s)^2 + x_s <-> m = (q - x_s) / (p - u_s)^2
plot(xlims= (0, 40), ylims=(0, 40), legend=false)
for a in as[1:5:end]
    u_values = 0:0.1:40
    u_s, x_s = model5(a, fit.param)
    m = (19 - x_s) / u_s^2
    x_values = m * (u_values .- u_s).^2 .+ x_s
    display(plot!(x_values, u_values, lw=2, alpha=0.5))
end


p = [thermostat.a => 0.1, thermostat.b => 0.9, thermostat.v_h => 40, thermostat.x_low => 19, thermostat.x_high => 21]
sol = solve_ode(19, 0, p)

solution = hcat(sol.u...)
min_x, min_x_index = findmin(solution[1,:])
min_u, min_u_index = findmin(solution[2,:])
max_u, max_u_index = findmax(solution[2,:])

plot(sol, vars=(1,2))
scatter!([solution[1,min_x_index]], [solution[2,min_x_index]], label="Min x", color=:black, markersize=3)
scatter!([solution[1,min_u_index]], [solution[2,min_u_index]], label="Min u", color=:black, markersize=3)
scatter!([solution[1,max_u_index]], [solution[2,max_u_index]], label="Max u", color=:black, markersize=3)

f_1(u) = (u - solution[2,min_x_index])^2 + solution[1,min_x_index]
f_1(u) = (u - solution[2,min_x_index])^2 + solution[1,min_x_index]

function parabola(x_s, u_s, p, q)
    m = (q - x_s) / (p - u_s)^2
    return u -> m * (u .- u_s).^2 .+ x_s
end

f_1 = parabola(solution[1,min_x_index], solution[2,min_x_index], 0, 19)
f_2 = parabola(solution[1,min_x_index], solution[2,min_x_index], 50, solution[1,max_u_index])
u_1 = 0:0.1:solution[2, min_x_index]
plot!(f_1(u_1), u_1, label="f_1", color=:black, lw=2, alpha=0.5)
u_2 = solution[2, min_x_index]:0.1:solution[2, max_u_index]
plot!(f_2(u_2), u_2, label="f_2", color=:black, lw=2, alpha=0.5)