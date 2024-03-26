using Symbolics
using ControlSystemsBase
using DifferentialEquations, Plots, ModelingToolkit
include("utils.jl")

function pendulum(u, p, t)
    control = -p[1] * (u[1] - p[3]) - p[2] * (u[2] - p[4])
    du = similar(u)
    du[1] = u[2]
    du[2] = -g / L * sin(u[1]) - b / (m * L^2) * u[2] + control / (m * L^2)
    return du
end

function control_gains()
    A = [0 1; 0 -b/(m * L^2)]
    B = [0; 1/(m * L^2)]
    C = [1 0]
    D = 0
    sys = ss(A, B, C, D)
    Q = [1 0; 0 1]
    R = 0.001
    K = lqr(sys,Q,R)
    return K
end

L = 1.0
g = 9.81
m = 1.0
b = 0.5

K = control_gains()
p = [K[1], K[2], π/2, 0.0]
u₀ = [π/2-0.2, -0.1]
prob = ODEProblem(pendulum, u₀, tspan, p)
sol = solve(prob,Tsit5())
plot(
    plot(sol, vars=(0,1)), plot(sol, vars=(0,2)), layout=(2,1), linewidth=2
)
plot(sol, vars=(1,2))
tspan = (0.0, 10.0)
region = [π/2-0.5 π/2+0.5; -0.8 0.8]
# invariant(x) = region[1,1] <= x[1] <= region[1,2] && region[2,1] <= x[2] <= region[2,2]
invariant(x) = region[1,1] <= x[1] <= region[1,2] && region[2,1] <= x[2] <= region[2,2] && -0.1 * (x[2] - region[2,1]) * (region[2,2] - x[2]) + region[1,1] + 0.1 <= x[1]
samples = sample_invariant(invariant, region, 2000)
solutions = solve_ode.(Ref(pendulum), eachcol(samples), Ref(tspan), Ref(p))
# plot_solution(samples, solutions)
plot_samples(samples, solutions)
solutions = solve_ode(pendulum,[region[1,2], region[2,2]], tspan, p)
# plot_solution(samples, solutions)
plot_solution!([region[1,2], region[2,2]], [solutions])

solutions = solve_ode(pendulum,[region[1,1]+0.1, region[2,1]], tspan, p)
# plot_solution(samples, solutions)
plot_solution!([region[1,1], region[2,1]], [solutions])
f2(x) = -0.1 * (x - region[2,1]) * (region[2,2] - x) + region[1,1] + 0.1
u_2 = region[2,1]:0.01:region[2,2]
u_1 = f2.(u_2)
plot!(u_1, u_2, label="Invariant", lw=2, color=:black)