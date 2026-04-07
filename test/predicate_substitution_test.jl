# ═══════════════════════════════════════════════════════════════════════════════
#              Tests for Predicate Substitution (Uniform Substitution)
#
# Following Platzer's definition:
#   σ(p(θ)) = {· ↦ σθ}∅ σp(·)   with FV(σp(·)) ∩ U = ∅
# ═══════════════════════════════════════════════════════════════════════════════

using Elenchos
using Elenchos.Kernel
using Elenchos.Syntax
using Test

# ─────────────────────────────────────────────────────────────────────────────
#  Setup: variables, predicates, function symbols
# ─────────────────────────────────────────────────────────────────────────────

x = Variable("x")
y = Variable("y")
z = Variable("z")

P_sym = PredicateSymbol("P")
Q_sym = PredicateSymbol("Q")

zero = Constant(0)
one  = Constant(1)

# ═══════════════════════════════════════════════════════════════════════════════
#  SECTION 1: Substitution Construction
# ═══════════════════════════════════════════════════════════════════════════════

@testset "Substitution Construction" begin

    @testset "Backward compatible: FunctionSymbol pairs" begin
        σ = Substitution(_x_sym => x)
        @test haskey(σ.bindings, _x_sym)
        @test isempty(σ.pred_bindings)
    end

    @testset "Backward compatible: Dict{FunctionSymbol,Term}" begin
        d = Dict{FunctionSymbol,Term}(_x_sym => x, _y_sym => y)
        σ = Substitution(d)
        @test length(σ.bindings) == 2
        @test isempty(σ.pred_bindings)
    end

    @testset "PredicateSymbol pairs only" begin
        A = P_sym(x)  # a formula
        σ = Substitution(_P_sym => A)
        @test isempty(σ.bindings)
        @test haskey(σ.pred_bindings, _P_sym)
        @test σ.pred_bindings[_P_sym] == A
    end

    @testset "Mixed pairs: FunctionSymbol + PredicateSymbol" begin
        A = LessThan(x, zero)
        σ = Substitution(_x_sym => y, _P_sym => A)
        @test σ.bindings[_x_sym] == y
        @test σ.pred_bindings[_P_sym] == A
    end

    @testset "Empty substitution" begin
        σ = Substitution()
        @test isempty(σ.bindings)
        @test isempty(σ.pred_bindings)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#  SECTION 2: Nullary Predicate Substitution (σ(p()) = σp)
# ═══════════════════════════════════════════════════════════════════════════════

@testset "Nullary Predicate Substitution" begin

    @testset "Replace _P_sym() with a concrete formula" begin
        # _P_sym() is a nullary predicate application
        original = _P_sym()
        target = LessThan(x, zero)   # x < 0
        σ = Substitution(_P_sym => target)
        @test substitute(original, σ) == target
    end

    @testset "Replace _Q_sym() with a concrete formula" begin
        original = _Q_sym()
        target = Implies(P_sym(x), P_sym(y))
        σ = Substitution(_Q_sym => target)
        @test substitute(original, σ) == target
    end

    @testset "Replace inside Not" begin
        original = Not(_P_sym())    # ¬A
        target = LessThan(x, y)     # x < y
        σ = Substitution(_P_sym => target)
        @test substitute(original, σ) == Not(target)
    end

    @testset "Replace inside Implies" begin
        original = Implies(_P_sym(), _Q_sym())   # A → B
        A = LessThan(x, zero)
        B = LessThan(zero, y)
        σ = Substitution(_P_sym => A, _Q_sym => B)
        @test substitute(original, σ) == Implies(A, B)
    end

    @testset "Replace inside And (defined connective)" begin
        # And(A,B) = Not(Implies(A, Not(B)))
        original = And(_P_sym(), _Q_sym())
        A = LessThan(x, y)
        B = LessThan(y, z)
        σ = Substitution(_P_sym => A, _Q_sym => B)
        @test substitute(original, σ) == And(A, B)
    end

    @testset "Unsubstituted predicate: recurse into args only" begin
        # R(x) with no substitution for R — should be unchanged
        R_sym = PredicateSymbol("R")
        original = R_sym(x)
        σ = Substitution(_P_sym => LessThan(y, zero))
        @test substitute(original, σ) == R_sym(x)
    end

    @testset "Unsubstituted predicate: term args get substituted" begin
        # R(_x) with _x_sym => y — the term arg should be substituted
        R_sym = PredicateSymbol("R")
        original = R_sym(_x_sym())
        σ = Substitution(_x_sym => y)
        @test substitute(original, σ) == R_sym(y)
    end

    @testset "Mixed: predicate + function symbol substitution" begin
        # _P_sym() with _P_sym => (x < 0), plus _x_sym => y
        original = Implies(_P_sym(), LessThan(_x_sym(), zero))
        σ = Substitution(_x_sym => y, _P_sym => LessThan(x, one))
        result = substitute(original, σ)
        @test result == Implies(LessThan(x, one), LessThan(y, zero))
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#  SECTION 3: N-ary Predicate Substitution (σ(p(θ)) = {· ↦ σθ}∅ σp(·))
# ═══════════════════════════════════════════════════════════════════════════════

@testset "N-ary Predicate Substitution" begin

    @testset "Unary predicate: p(x) with p ↦ (· < 0)" begin
        # p maps to a formula with Hole(1): Hole(1) < 0
        ctx = LessThan(Hole(1), zero)
        σ = Substitution(_P_sym => ctx)
        result = substitute(_P_sym(x), σ)
        @test result == LessThan(x, zero)
    end

    @testset "Unary predicate: substitute arg too" begin
        # p(_x) with _x ↦ y, p ↦ (· < 0)
        # σ(p(_x)) = {· ↦ σ(_x)}∅ σp(·) = {· ↦ y}∅ (· < 0) = y < 0
        ctx = LessThan(Hole(1), zero)
        σ = Substitution(_x_sym => y, _P_sym => ctx)
        result = substitute(_P_sym(_x_sym()), σ)
        @test result == LessThan(y, zero)
    end

    @testset "Unary predicate: Hole in nested formula" begin
        # p ↦ ¬(Hole(1) < Hole(1))   i.e. p(t) = ¬(t < t)
        ctx = Not(LessThan(Hole(1), Hole(1)))
        σ = Substitution(_P_sym => ctx)
        result = substitute(_P_sym(Sum(x, y)), σ)
        @test result == Not(LessThan(Sum(x, y), Sum(x, y)))
    end

    @testset "Unary predicate inside implication" begin
        # p(x) → p(y)  with p ↦ (· < 0)
        ctx = LessThan(Hole(1), zero)
        σ = Substitution(_P_sym => ctx)
        original = Implies(_P_sym(x), _P_sym(y))
        result = substitute(original, σ)
        @test result == Implies(LessThan(x, zero), LessThan(y, zero))
    end

    @testset "Binary predicate: p(x,y) with Hole(1) and Hole(2)" begin
        # Two-argument predicate: p maps to Hole(1) < Hole(2)
        ctx = LessThan(Hole(1), Hole(2))
        σ = Substitution(_P_sym => ctx)
        result = substitute(_P_sym(x, y), σ)
        @test result == LessThan(x, y)
    end

    @testset "Binary predicate: args are substituted first" begin
        ctx = LessThan(Hole(1), Hole(2))
        σ = Substitution(_x_sym => Sum(x, one), _y_sym => zero, _P_sym => ctx)
        result = substitute(_P_sym(_x_sym(), _y_sym()), σ)
        @test result == LessThan(Sum(x, one), zero)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#  SECTION 5: Admissibility (Variable Capture Prevention)
# ═══════════════════════════════════════════════════════════════════════════════

@testset "Predicate Substitution Admissibility" begin

    @testset "Nullary predicate under quantifier: safe" begin
        # ∀x. P()  with P ↦ (y < 0) — y is free but not bound by ∀x
        original = Forall(x, _P_sym())
        σ = Substitution(_P_sym => LessThan(y, zero))
        result = substitute(original, σ)
        @test result == Forall(x, LessThan(y, zero))
    end

    @testset "Nullary predicate under quantifier: capture rejected" begin
        # ∀x. P()  with P ↦ (x < 0) — x is captured by ∀x!
        original = Forall(x, _P_sym())
        σ = Substitution(_P_sym => LessThan(x, zero))
        @test_throws ArgumentError substitute(original, σ)
    end

    @testset "N-ary predicate under quantifier: safe" begin
        # ∀x. P(y)  with P ↦ (· < z) — z not bound by ∀x
        ctx = LessThan(Hole(1), z)
        original = Forall(x, _P_sym(y))
        σ = Substitution(_P_sym => ctx)
        result = substitute(original, σ)
        @test result == Forall(x, LessThan(y, z))
    end

    @testset "N-ary predicate under quantifier: capture rejected" begin
        # ∀x. P(y)  with P ↦ (· < x) — x is captured by ∀x!
        ctx = LessThan(Hole(1), x)
        original = Forall(x, _P_sym(y))
        σ = Substitution(_P_sym => ctx)
        @test_throws ArgumentError substitute(original, σ)
    end

    @testset "Function substitution still checks admissibility" begin
        # ∀x. (_x < 0)  with _x ↦ x — x captured by ∀x
        original = Forall(x, LessThan(_x_sym(), zero))
        σ = Substitution(_x_sym => x)
        @test_throws ArgumentError substitute(original, σ)
    end
end


# ═══════════════════════════════════════════════════════════════════════════════
#  SECTION 7: Backward Compatibility
# ═══════════════════════════════════════════════════════════════════════════════

@testset "Backward Compatibility" begin

    @testset "Pure function symbol substitution unchanged" begin
        original = LessThan(_x_sym(), _y_sym())
        σ = Substitution(_x_sym => x, _y_sym => Sum(x, one))
        result = substitute(original, σ)
        @test result == LessThan(x, Sum(x, one))
    end

    @testset "N-ary function symbol (context) substitution unchanged" begin
        ctx = Sum(Hole(1), y)
        σ = Substitution(_C_sym => ctx)
        result = substitute(_C_sym(x), σ)
        @test result == Sum(x, y)
    end

    @testset "Axiom instantiation unchanged" begin
        # AX_EQ_REFL: _x = _x
        σ = Substitution(_x_sym => Sum(x, zero))
        result = substitute(AX_EQ_REFL.formula, σ)
        @test result == Equals(Sum(x, zero), Sum(x, zero))
    end

    @testset "Empty substitution is identity" begin
        σ = Substitution()
        formula = Implies(LessThan(x, y), Not(LessThan(y, x)))
        @test substitute(formula, σ) == formula
    end

    @testset "Callable syntax works" begin
        σ = Substitution(_P_sym => LessThan(x, zero))
        @test σ(_P_sym()) == LessThan(x, zero)
    end
end
