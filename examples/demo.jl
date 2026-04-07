using Elenchos

# ══════════════════════════════════════════════════════════════════════════════
# Propositional Logic: Simple Identity
# ══════════════════════════════════════════════════════════════════════════════

@preds A B C
p1 = start_proof((A(), B(), C()) ⊢ A()) |> id()
print_proof_tree(p1)

# ──────────────────────────────────────────────────────────────────────────────

start_proof(() ⊢ (A(), A())) |> apply(p1, target_idx=Cons(2))

# ══════════════════════════════════════════════════════════════════════════════
# Propositional Logic: Peirce's Law
# ══════════════════════════════════════════════════════════════════════════════

p2 = start_proof(⊢(((A() → B()) → A()) → A()))
p2 = p2 |> implies_right()
p2 = p2 |> implies_left()
p2 = p2 |> implies_right()
p2 = p2 |> id() |> id()
print_proof_tree(p2)

# ──────────────────────────────────────────────────────────────────────────────

p4 = start_proof(A() → B()) |> implies_right()

# ══════════════════════════════════════════════════════════════════════════════
# Linear Arithmetic: Fact Construction and Normalization
# ══════════════════════════════════════════════════════════════════════════════

@vars x y z

seq = (x + y ≤ 2, 1 ≤ y) ⊢ (x ≤ 2)

f1 = Fact(x + y ≤ 2)
f1.proof
f2 = Fact(1 ≤ y)
f3 = normalize(f1 + -1 * f2)
f3.proof

normalize((x + y + (-1) * y))

f4 = f1 + f2
f4.proof

# ──────────────────────────────────────────────────────────────────────────────

p = start_proof(seq)
p = p |> trans(Constant(1))
p = p |> apply(normalize(1 * f1 + -1 * f2))
p = p |> Repeat(id())
p = p |> arith()

# ══════════════════════════════════════════════════════════════════════════════
# Linear Arithmetic: Advanced Automation with Farkas Witnesses
# ══════════════════════════════════════════════════════════════════════════════

# A^T x ≤ b ⊢ c^T x ≤ d
A, b, c, d = linear_form(seq)

λ, c_max = farkas_witness(seq)

p = start_proof(seq)
p = p |> trans(c_max)
p = p |> apply(λ' * ante(p))
p = p |> Repeat(id())
p = p |> arith()

start_proof(seq) |> lin_arith()

# ══════════════════════════════════════════════════════════════════════════════
# Linear Arithmetic: Large-Scale Proof
# ══════════════════════════════════════════════════════════════════════════════

vs = [Variable("x$i") for i in 1:50]
vs

in_eqs = [1 // i * vs[i] ≤ (3 * i + 1) // 3 for i in 1:50]
fact = normalize(sum(Fact.(in_eqs)))

seq = (in_eqs...,) ⊢ (fact.left ≤ fact.right)

p = start_proof(seq) |> lin_arith()

# ══════════════════════════════════════════════════════════════════════════════
# Hybrid: Propositional + Linear Arithmetic
# ══════════════════════════════════════════════════════════════════════════════

fml = ((x + y ≤ 2) ∧ (1 ≤ y)) → (x ≤ 2)
p = start_proof(fml)
prop_strat = Repeat(Choice(and_left(), implies_right()))
p |> prop_strat |> lin_arith()

# ══════════════════════════════════════════════════════════════════════════════
# Strategies: Depth-First Search with Backtracking
# ══════════════════════════════════════════════════════════════════════════════

@vars x

seq = ((x ≤ 2)) ⊢ ((x ≤ 3) ∨ (x ≤ 0))
p = start_proof(seq)
strategy = Repeat(Choice(lin_arith(target_idx=nothing), prop()))
p_solved, trace = solve_dfs(strategy, p)
start_proof(seq) |> or_right() |> lin_arith(target_idx=Cons(2))

print_tactic_proof(trace, start_proof(seq))