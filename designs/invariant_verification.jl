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
J(p,q) = p * heater.x > 0 + q
for _ in 1:100
    # Invariant template
    # Select sampling strategy
    samples = sample(J(p,q), 100)
    trajectories = solve(heater, samples, (0.0, 10.0))
    if trajectories ∈ Q
        # Return refinement of J
        result = prove(verification, J)
        if result
            println("Proved")
            break
        end
    else
        p = p + 1
        q = q + 1
        qe_1 = quantifier_elimination(P -> J)
        qe_2 = quantifier_elimination(J -> Q)
    end
end
plot(trajectories, vars=(t, heater.x), label="x")
prove(verification, J)

# 1. Concept: Parametric formulas. Difference between numeric and symbolic variables
f1 = p * x^2 + q * x + 1 > 0
# 2. Concept: Substitution for semialgebraic formulas (stable transformation: formula -> formula)
f2 = subst(f1, [p => 1, q => 1])
# 3. Concept: Sampling. Sample all free variables in the formula (semi-algebraic set)
samples = sample(f2, n=100, method = "uniform")
# 4. Concept: Solve the ODE with the samples
trajectories = solve.(heater, samples, (0.0, 10.0)) # Returns an array of trajectories with x -> [x(t_1), x(t_2), ...], y -> [y(t_1), y(t_2), ...],...
# 5. Concept: Check if the trajectories are in the invariant
all(trajectory -> all(Q.(trajectory.u)), trajectories)
# or subst(Q, trajectories)
# 6. Concept: Update. Update parametric formula
# f3 = refine(f2, trajectories)
p_new = refine(J, p, trajectories)
# 7. Concept: Check propositonal formula
check(J(p) -> [heater]J(p)) # For star-free programs
# 8. Concept: Quantifier elimination
qe = quantifier_elimination(P -> f3)
# 9. Concept: Generate invariant template. Symbolic regression task?

# 10. Concept: Fromula evaluation
f1(1,1)(1)
# 11. Concept: Refinement of invariant
f1 = and(f1, f2)

# 12. Concept: Counterexample
counter_example(J -> [heater]J)

# 13. Concept: Check with invariant
check(J -> [heater]J, invariant = J)