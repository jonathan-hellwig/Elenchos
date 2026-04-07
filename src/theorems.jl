module Theorems
using ..Kernel
using ..Syntax
using ..BaseTactics
using ..BaseTactics: start_proof, apply, comm, rewrite

export THM_EQ_SYMM, THM_EQ_TRANS
export THM_CONG_SUM_LEFT, THM_CONG_SUM_RIGHT, THM_CONG_PRODUCT_LEFT, THM_CONG_PRODUCT_RIGHT, THM_CONG_ADD_LEFT_RIGHT_EQUAL, THM_CONG_SUB_LEFT_RIGHT_EQUAL
export THM_EQ_ANTISYMMETRY
export THM_ADD_ID_LEFT, THM_ADD_LEFT_ASSOCIATIVE, THM_ADD_LEFT_COMMUTATIVE
export THM_MUL_ID_LEFT, THM_MUL_ASSO_REV, THM_MUL_LEFT_COMMUTATIVE
export THM_DIS_RIGHT, THM_DIS_REV
export THM_MUL_ZERO_LEFT, THM_MUL_ZERO
export THM_EQ_SUB_ZERO
export THM_SUB_ZERO_EQ
export THM_COLLECT_BASE, THM_COLLECT_BASE_TAIL, THM_COLLECT_LEFT, THM_COLLECT_RIGHT, THM_COLLECT_LEFT_TAIL, THM_COLLECT_RIGHT_TAIL, THM_COLLECT_BOTH, THM_COLLECT_BOTH_TAIL

# ─────────────────────────────────────────────────────────────────────────────
# 1. Equality
# ─────────────────────────────────────────────────────────────────────────────

const THM_EQ_SYMM = let
    p = start_proof((_x ~ _y) → (_y ~ _x))
    p = p |> implies_right()
    p = p |> rewrite(_x, [1])
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
end

const THM_EQ_TRANS = let
    p = start_proof((_x ~ _z) ∧ (_z ~ _y) → (_x ~ _y))
    p = p |> implies_right()
    p = p |> and_left()
    p = p |> rewrite(_z, [1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> id()
end

# ─────────────────────────────────────────────────────────────────────────────
# 2. Congruence Properties
# ─────────────────────────────────────────────────────────────────────────────
const THM_CONG_SUM_LEFT = let
    p = start_proof((_x ~ _y) → ((_x + _z) ~ (_y + _z)))
    p = p |> implies_right()
    p = p |> rewrite(_y, [1, 1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_CONG_SUM_RIGHT = let
    p = start_proof((_x ~ _y) → ((_z + _x) ~ (_z + _y)))
    p = p |> implies_right()
    p = p |> rewrite(_y, [1, 2])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_CONG_PRODUCT_LEFT = let
    σ = Substitution(_C_sym => Hole(1) * _z)
    p = start_proof((_x ~ _y) → ((_x * _z) ~ (_y * _z)))
    p = p |> implies_right()
    p = p |> apply(instantiate(rule(AX_CONG_CONTEXT), σ))
    p = p |> id()
    p
end

const THM_CONG_PRODUCT_RIGHT = let
    p = start_proof((_x ~ _y) → ((_z * _x) ~ (_z * _y)))
    p = p |> implies_right()
    p = p |> rewrite(_y, [1, 2])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_CONG_ADD_LEFT_RIGHT_EQUAL = let
    p = start_proof(((_x ~ _y) ∧ (_z ~ _w)) → ((_x + _z) ~ (_y + _w)))
    p = p |> implies_right()
    p = p |> and_left()
    p = p |> rewrite(_y, [1, 1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> rewrite(_w, [1, 2])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_CONG_SUB_LEFT_RIGHT_EQUAL = let
    p = start_proof(((_x ~ _y) ∧ (_z ~ _w)) → (Difference(_x, _z) ~ Difference(_y, _w)))
    p = p |> implies_right()
    p = p |> and_left()
    p = p |> rewrite(_y, [1, 1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> rewrite(_w, [1, 2])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> id()
    p = p |> apply(AX_EQ_REFL)
    p
end


# ─────────────────────────────────────────────────────────────────────────────
# 3. Logic and Order (Equality Bridge)
# ─────────────────────────────────────────────────────────────────────────────
const THM_EQ_ANTISYMMETRY = let
    p = start_proof(((_x ≤ _y) ∧ (_y ≤ _x)) → (_x ~ _y))
    fml = ((_x < _y) ∨ ((_x ~ _y) ∨ (_y < _x)))
    p = p |> implies_right()
    p = p |> and_left()
    p = p |> cut(fml)
    p = p |> weaken_all_but(fml)
    p = p |> exact(AX_LT_TRICHOTOMY)
    p = p |> or_left()
    p = p |> not_left(target_idx=Ante(2))
    p = p |> id()
    p = p |> or_left()
    p = p |> id()
    p = p |> not_left()
    p = p |> id()
    p
end


# ─────────────────────────────────────────────────────────────────────────────
# 4. Additive Properties
# ─────────────────────────────────────────────────────────────────────────────
const THM_ADD_ID_LEFT = let
    p = start_proof(0 + _x ~ _x)
    p = p |> rewrite(_x + 0, [1])
    p = p |> apply(AX_ADD_COMM)
    p = p |> apply(AX_ADD_ID)
    p
end

const THM_ADD_LEFT_ASSOCIATIVE = let
    p = start_proof(_x + (_y + _z) ~ (_x + _y) + _z)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(AX_ADD_ASSO)
    p
end

const THM_ADD_LEFT_COMMUTATIVE = let
    p = start_proof(_x + (_y + _z) ~ _y + (_x + _z))
    p = p |> rewrite((_x + _y) + _z, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> rewrite((_y + _x) + _z, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite(_x + _y, [1, 1])
    p = p |> comm()
    p = p |> apply(AX_EQ_REFL)
    p
end


# ─────────────────────────────────────────────────────────────────────────────
# 5. Multiplicative Properties
# ─────────────────────────────────────────────────────────────────────────────
const THM_MUL_ID_LEFT = let
    p = start_proof(_x * 1 ~ _x)
    p = p |> rewrite(1 * _x, [1])
    p = p |> apply(AX_MUL_COMM)
    p = p |> apply(AX_MUL_ID)
    p
end

const THM_MUL_ASSO_REV = let
    p = start_proof(_x * (_y * _z) ~ (_x * _y) * _z)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(AX_MUL_ASSO)
    p
end

const THM_MUL_LEFT_COMMUTATIVE = let
    p = start_proof(_x * (_y * _z) ~ _y * (_x * _z))
    p = p |> rewrite((_x * _y) * _z, [1])
    p = p |> apply(AX_MUL_ASSO)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> rewrite((_y * _x) * _z, [1])
    p = p |> apply(AX_MUL_ASSO)
    p = p |> rewrite(_x * _y, [1, 1])
    p = p |> comm()
    p = p |> apply(AX_EQ_REFL)
    p
end


# ─────────────────────────────────────────────────────────────────────────────
# 6. Distributivity and Zero Properties
# ─────────────────────────────────────────────────────────────────────────────
const THM_DIS_RIGHT = let
    p = start_proof((_y + _z) * _x ~ (_y * _x + _z * _x))
    p = p |> rewrite(_x * (_y + _z), [1])
    p = p |> comm()
    p = p |> rewrite(_x * _y, [2, 1])
    p = p |> comm()
    p = p |> rewrite(_x * _z, [2, 2])
    p = p |> comm()
    p = p |> apply(AX_DIS)
    p
end

const THM_DIS_REV = let
    p = start_proof((_y + _z) * _x ~ _y * _x + _z * _x)
    p = p |> rewrite(_x * (_y + _z), [1])
    p = p |> comm()
    p = p |> rewrite(_x * _y, [2, 1])
    p = p |> comm()
    p = p |> rewrite(_x * _z, [2, 2])
    p = p |> comm()
    p = p |> apply(AX_DIS)
end

const THM_MUL_ZERO_LEFT = let
    p = start_proof(0 * _x ~ 0)
    p = p |> rewrite((Constant(1) + Constant(-1)) * _x, [1])
    p = p |> apply(rule(THM_CONG_PRODUCT_LEFT))
    p = p |> apply(rule(THM_EQ_ANTISYMMETRY))
    p = p |> and_right()
    p = p |> not_right()
    p = p |> arith_left()
    p = p |> not_right()
    p = p |> arith_left()
    p = p |> rewrite(1 * _x + -1 * _x, [1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_DIS_REV)
    p = p |> rewrite(1 * _x => _x, ExactMatch)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(AX_MUL_ID)
    p = p |> apply(AX_ADD_INV)
    p
end


const THM_MUL_ZERO = let
    p = start_proof(Equals(Product(_x, ZERO), ZERO))
    p = p |> rewrite(0 * _x, [1])
    p = p |> comm()
    p = p |> apply(THM_MUL_ZERO_LEFT)
    p
end

# ─────────────────────────────────────────────────────────────────────────────
# 7. Subtraction & Difference Properties
# ─────────────────────────────────────────────────────────────────────────────
const THM_EQ_SUB_ZERO = let
    p = start_proof((_x ~ _y) → (Difference(_x, _y) ~ 0))
    p = p |> implies_right()
    p = p |> rewrite(_x, [1, 2])
    p = p |> id()
    p = p |> rewrite(_x + (-1) * _x, [1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(AX_DIFF)
    p = p |> apply(AX_ADD_INV)
    p
end

const THM_SUB_ZERO_EQ = let
    p = start_proof((Difference(_x, _y) ~ 0) → (_x ~ _y))
    p = p |> implies_right()
    p = p |> cut((_x - _y ~ 0) → ((_x - _y) + _y ~ 0 + _y))
    p = p |> apply(THM_CONG_SUM_LEFT)
    p = p |> implies_left()
    p = p |> id()
    p = p |> weaken_left(fml=_x - _y ~ 0)
    p = p |> rewrite(_y, Ante(1), [2])
    p = p |> apply(THM_ADD_ID_LEFT)
    p = p |> rewrite(_x + (-1) * _y, Ante(1), [1, 1])
    p = p |> apply(AX_DIFF)
    p = p |> rewrite(_x + ((-1) * _y + _y), Ante(1), [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite(_y + (-1) * _y, Ante(1), [1, 2])
    p = p |> comm()
    p = p |> rewrite(Constant(0), Ante(1), [1, 2])
    p = p |> apply(AX_ADD_INV)
    p = p |> rewrite(_x, Ante(1), [1])
    p = p |> apply(AX_ADD_ID)
    p = p |> id()
    p
end


# ─────────────────────────────────────────────────────────────────────────────
# 8. Coefficient Collection (Normalization)
# ─────────────────────────────────────────────────────────────────────────────
const THM_COLLECT_BASE = let
    p = start_proof(_x + _x ~ 2 * _x)
    p = p |> rewrite(1 * _x, [1, 1])
    p = p |> apply(AX_MUL_ID)
    p = p |> rewrite(1 * _x, [1, 2])
    p = p |> apply(AX_MUL_ID)
    p = p |> rewrite((Constant(1) + 1), [2, 1])
    p = p |> apply(rule(THM_EQ_ANTISYMMETRY))
    p = p |> and_right()
    p = p |> not_right()
    p = p |> arith_left()
    p = p |> not_right()
    p = p |> arith_left()
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_DIS_REV)
    p
end

const THM_COLLECT_BASE_TAIL = let
    p = start_proof(_x + (_x + _y) ~ (2 * _x + _y))
    p = p |> rewrite((_x + _x) + _y, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite(2 * _x, [1, 1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_COLLECT_BASE)
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_COLLECT_LEFT = let
    p = start_proof((_z * _x + _x) ~ ((_z + 1) * _x))
    p = p |> rewrite(1 * _x, [1, 2])
    p = p |> apply(AX_MUL_ID)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_DIS_REV)
    p
end

const THM_COLLECT_RIGHT = let
    p = start_proof((_x + _z * _x) ~ ((1 + _z) * _x))
    p = p |> rewrite(1 * _x, [1, 1])
    p = p |> apply(AX_MUL_ID)
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_DIS_REV)
    p
end

const THM_COLLECT_LEFT_TAIL = let
    p = start_proof((_z * _x + (_x + _y)) ~ (((_z + 1) * _x) + _y))
    p = p |> rewrite((_z * _x + _x) + _y, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite((_z + 1) * _x, [1, 1])
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_COLLECT_LEFT)
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_COLLECT_RIGHT_TAIL = let
    p = start_proof((_x + (_z * _x + _y)) ~ (((1 + _z) * _x) + _y))
    p = p |> rewrite((_x + _z * _x) + _y, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite(1 * _x, [1, 1, 1])
    p = p |> apply(AX_MUL_ID)
    p = p |> rewrite((1 + _z) * _x, [1, 1])
    p = p |> apply(THM_DIS_REV)
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_COLLECT_BOTH = let
    p = start_proof((_z * _x + _a * _x) ~ ((_z + _a) * _x))
    p = p |> apply(rule(THM_EQ_SYMM))
    p = p |> apply(THM_DIS_REV)
    p
end

const THM_COLLECT_BOTH_TAIL = let
    p = start_proof((_z * _x + (_a * _x + _y)) ~ (((_z + _a) * _x) + _y))
    p = p |> rewrite((_z * _x + _a * _x) + _y, [1])
    p = p |> apply(AX_ADD_ASSO)
    p = p |> rewrite((_z + _a) * _x, [1, 1])
    p = p |> apply(THM_DIS_REV)
    p = p |> apply(AX_EQ_REFL)
    p
end

const THM_LEQ_SCALE_RIGHT = let
    p = start_proof(Implies(LessOrEqual(ZERO, _z), Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_x, _z), Product(_y, _z)))))
    p = p |> implies_right()
    p = p |> implies_right()
    p = p |> rewrite(_z * _x, [1])
    p = p |> apply(AX_MUL_COMM)
    p = p |> rewrite(_z * _y, [2])
    p = p |> apply(AX_MUL_COMM)
    p = p |> apply(AX_LEQ_SCALE_LEFT)
    p = p |> id()
    p = p |> id()
end

const THM_LEQ_REFL = let
    p = start_proof(LessOrEqual(_x, _x))
    # LessOrEqual(x, x) expands to Not(LessThan(x, x))
    p = p |> apply(AX_LT_IRREFLEXIVITY)
    p
end

const THM_LEQ_SCALE_RIGHT_NEG = let
    p = start_proof(Implies(LessOrEqual(_z, ZERO), Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_y, _z), Product(_x, _z)))))
    p = p |> implies_right()
    p = p |> implies_right()
    # Commute the left side of the inequality
    p = p |> rewrite(_z * _y, [1])
    p = p |> apply(AX_MUL_COMM)
    # Commute the right side of the inequality
    p = p |> rewrite(_z * _x, [2])
    p = p |> apply(AX_MUL_COMM)
    # Apply the left-scaling negative axiom
    p = p |> apply(AX_LEQ_SCALE_LEFT_NEG)
    p = p |> id()
    p = p |> id()
    p
end

end