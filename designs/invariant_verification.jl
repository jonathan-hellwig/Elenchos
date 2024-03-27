using ModelingToolkit
using Plots
using DifferentialEquations
using ModelingToolkit: t_nounits as t, D_nounits as D

@mtkmodel Heater begin
    @variables begin
        x(t)
    end
    @equations begin
        D(x) ~ -x
    end
end

@mtkbuild heater = Heater()
# P -> [x'=-x]Q
P = heater.x > 0
Q = heater.x > 0
verification = VerificationProblem(heater, P, Q, (0.0, 10.0))

# Goal: Find the right abstraction to interact with the proof
p = 1
q = 1
J = p * heater.x > 0 + q
for _ in 1:100
    # Invariant template
    # Select sampling strategy
    samples = sample(J, 100)
    trajectories = solve(heater, samples, (0.0, 10.0))
    if trajectories[end] ∈ Q
        # Return refinement of J
        result = prove(verification, J)
        if result
            println("Proved")
            break
        end
    else
        # Question: How do I update p and q?
        p = p + 1
        q = q + 1
        prove(P, J)
        prove(J, Q)
    end
end
plot(trajectories, vars=(t, heater.x), label="x")
prove(verification, J)