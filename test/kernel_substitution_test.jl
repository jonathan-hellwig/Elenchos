using Test

# Test file for kernel ground evaluation and positive constant rules
# This tests Phase 2 implementations

using Elenchos
using Elenchos.Kernel
using Elenchos.Kernel: has_clash

@testset "Kernel Ground Evaluation" begin
    x = Variable("x")
    y = Variable("y")
    z = Variable("z")
    c0 = Constant(0)
    c1 = Constant(1)
    c2 = Constant(2)
    c3 = Constant(3)
    c5 = Constant(5)

    @testset "Uniform Substitution Admissibility" begin
        # Test Platzer's uniform substitution with taboo variables
        f_sym = FunctionSymbol("f")
        f = f_sym()  # nullary function application

        # Valid: substitute f → 1 inside ∀x. f ≤ y  (no capture)
        formula1 = Forall(x, LessThan(f, y))
        σ1 = Substitution(f_sym => c1)
        result1 = substitute(formula1, σ1)
        @test result1 == Forall(x, LessThan(c1, y))

        # Valid: substitute f → y inside ∀x. f ≤ x  (y not bound)
        formula2 = Forall(x, LessThan(f, x))
        σ2 = Substitution(f_sym => y)
        result2 = substitute(formula2, σ2)
        @test result2 == Forall(x, LessThan(y, x))
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        c0 = Constant(0)
        c1 = Constant(1)
        c2 = Constant(2)
        c3 = Constant(3)
        c5 = Constant(5)
        # INADMISSIBLE: substitute f → x inside ∀x. f ≤ y  (x is bound!)
        formula3 = Forall(x, LessThan(f, y))
        σ3 = Substitution(f_sym => x)
        @test_throws ArgumentError substitute(formula3, σ3)

        # Valid outside quantifier, inadmissible inside
        outer = LessThan(f, y)  # f ≤ y  (no quantifier)
        @test substitute(outer, σ3) == LessThan(x, y)  # Works at top level

        # Nested quantifiers: ∀x.∀y. f ≤ x
        nested = Forall(x, Forall(y, LessThan(f, x)))
        @test_throws ArgumentError substitute(nested, Substitution(f_sym => x))  # x bound
        @test_throws ArgumentError substitute(nested, Substitution(f_sym => y))  # y bound
        @test substitute(nested, Substitution(f_sym => c1)) ==
              Forall(x, Forall(y, LessThan(c1, x)))  # constant ok
    end

    @testset "has_clash" begin
        @test has_clash(Sum(x, y), Set([x]))
        @test has_clash(Sum(x, y), Set([y]))
        @test !has_clash(Sum(x, y), Set([z]))
        @test !has_clash(Forall(x, Equals(Sum(x, y), z)), Set([x]))
        @test has_clash(Forall(x, Equals(Sum(x, y), z)), Set([y]))
    end

end

@testset "has_clash" begin

    # ── Fixtures ────────────────────────────────────────────────────────────
    x = Variable("x")
    y = Variable("y")
    z = Variable("z")
    w = Variable("w")
    c0 = Constant(0)
    c1 = Constant(1)
    c2 = Constant(2)
    f = FunctionSymbol("f")
    g = FunctionSymbol("g")
    P = PredicateSymbol("P")
    Q = PredicateSymbol("Q")

    # ── Constants and Holes ─────────────────────────────────────────────────
    @testset "Constant and Hole" begin
        @test !has_clash(c0, Set([x]))
        @test !has_clash(c1, Set([x, y, z]))
        @test !has_clash(c0, Set{Variable}())
        @test !has_clash(Hole(1), Set([x]))
        @test !has_clash(Hole(2), Set([x, y]))
        @test !has_clash(Hole(1), Set{Variable}())
    end

    # ── Variables ───────────────────────────────────────────────────────────
    @testset "Variable" begin
        @test has_clash(x, Set([x]))
        @test has_clash(y, Set([y]))
        @test !has_clash(x, Set([y]))
        @test !has_clash(x, Set{Variable}())
        # multiple taboo variables — only one needs to match
        @test has_clash(x, Set([x, y, z]))
        @test !has_clash(w, Set([x, y, z]))
    end

    # ── Arithmetic terms ────────────────────────────────────────────────────
    @testset "Sum" begin
        @test has_clash(Sum(x, y), Set([x]))
        @test has_clash(Sum(x, y), Set([y]))
        @test !has_clash(Sum(x, y), Set([z]))
        @test !has_clash(Sum(c1, c2), Set([x]))
        @test has_clash(Sum(x, Sum(y, z)), Set([z]))
        @test !has_clash(Sum(x, y), Set{Variable}())
        # left clash only
        @test has_clash(Sum(x, c1), Set([x]))
        # right clash only
        @test has_clash(Sum(c1, y), Set([y]))
    end

    @testset "Difference" begin
        @test has_clash(Difference(x, y), Set([x]))
        @test has_clash(Difference(x, y), Set([y]))
        @test !has_clash(Difference(x, y), Set([z]))
        @test !has_clash(Difference(c1, c2), Set([x]))
        @test has_clash(Difference(x, c1), Set([x]))
        @test has_clash(Difference(c1, y), Set([y]))
    end

    @testset "Product" begin
        @test has_clash(Product(x, y), Set([x]))
        @test has_clash(Product(x, y), Set([y]))
        @test !has_clash(Product(x, y), Set([z]))
        @test !has_clash(Product(c1, c2), Set([x]))
        @test has_clash(Product(x, c1), Set([x]))
        @test has_clash(Product(c1, y), Set([y]))
    end

    @testset "Division" begin
        @test has_clash(Division(x, y), Set([x]))
        @test has_clash(Division(x, y), Set([y]))
        @test !has_clash(Division(x, y), Set([z]))
        @test !has_clash(Division(c1, c2), Set([x]))
    end

    @testset "Power" begin
        @test has_clash(Power(x, Constant(2)), Set([x]))
        @test !has_clash(Power(x, Constant(2)), Set([y]))
        @test !has_clash(Power(c2, Constant(3)), Set([x]))
        # exponent is always a Constant — never a clash source
        @test !has_clash(Power(c1, Constant(2)), Set([x, y, z]))
        # nested base
        @test has_clash(Power(Sum(x, c1), Constant(2)), Set([x]))
        @test !has_clash(Power(Sum(c1, c2), Constant(2)), Set([x]))
    end

    @testset "FunctionApplication" begin
        # nullary
        @test !has_clash(FunctionApplication(f, ()), Set([x]))
        # unary
        @test has_clash(FunctionApplication(f, (x,)), Set([x]))
        @test !has_clash(FunctionApplication(f, (x,)), Set([y]))
        # binary
        @test has_clash(FunctionApplication(f, (x, y)), Set([x]))
        @test has_clash(FunctionApplication(f, (x, y)), Set([y]))
        @test !has_clash(FunctionApplication(f, (x, y)), Set([z]))
        # nested function applications
        inner = FunctionApplication(g, (z,))
        @test has_clash(FunctionApplication(f, (x, inner)), Set([z]))
        @test !has_clash(FunctionApplication(f, (x, inner)), Set([w]))
    end

    # ── Atomic formulas ─────────────────────────────────────────────────────
    @testset "LessThan" begin
        @test has_clash(LessThan(x, y), Set([x]))
        @test has_clash(LessThan(x, y), Set([y]))
        @test !has_clash(LessThan(x, y), Set([z]))
        @test !has_clash(LessThan(c1, c2), Set([x]))
        @test has_clash(LessThan(Sum(x, c1), c2), Set([x]))
    end

    @testset "Equals" begin
        @test has_clash(Equals(x, y), Set([x]))
        @test has_clash(Equals(x, y), Set([y]))
        @test !has_clash(Equals(x, y), Set([z]))
        @test !has_clash(Equals(c1, c2), Set([x]))
        @test has_clash(Equals(x, x), Set([x]))
    end

    @testset "PredicateApplication" begin
        # nullary
        @test !has_clash(PredicateApplication(P, ()), Set([x]))
        # unary
        @test has_clash(PredicateApplication(P, (x,)), Set([x]))
        @test !has_clash(PredicateApplication(P, (x,)), Set([y]))
        # binary
        @test has_clash(PredicateApplication(P, (x, y)), Set([y]))
        @test !has_clash(PredicateApplication(P, (x, y)), Set([z]))
        # nested terms
        @test has_clash(PredicateApplication(P, (Sum(x, c1),)), Set([x]))
        @test !has_clash(PredicateApplication(P, (Sum(c1, c2),)), Set([x]))
    end

    # ── Propositional connectives ────────────────────────────────────────────
    @testset "Not" begin
        @test has_clash(Not(Equals(x, c1)), Set([x]))
        @test !has_clash(Not(Equals(x, c1)), Set([y]))
        @test !has_clash(Not(Equals(c1, c2)), Set([x]))
        # double negation
        @test has_clash(Not(Not(Equals(x, c1))), Set([x]))
        @test !has_clash(Not(Not(Equals(c1, c2))), Set([x]))
    end

    @testset "Implies" begin
        @test has_clash(Implies(Equals(x, c1), Equals(y, c1)), Set([x]))
        @test has_clash(Implies(Equals(x, c1), Equals(y, c1)), Set([y]))
        @test !has_clash(Implies(Equals(x, c1), Equals(y, c1)), Set([z]))
        # clash only in antecedent
        @test has_clash(Implies(Equals(x, c1), Equals(c1, c2)), Set([x]))
        # clash only in consequent
        @test has_clash(Implies(Equals(c1, c2), Equals(y, c1)), Set([y]))
        # no clash in either
        @test !has_clash(Implies(Equals(c1, c2), Equals(c2, c1)), Set([x, y]))
    end

    # ── Quantifiers ─────────────────────────────────────────────────────────
    @testset "Forall — basic shadowing" begin
        # x bound by Forall — taboo x should not clash
        @test !has_clash(Forall(x, Equals(Sum(x, y), z)), Set([x]))
        # y is free — taboo y clashes
        @test has_clash(Forall(x, Equals(Sum(x, y), z)), Set([y]))
        # z is free — taboo z clashes
        @test has_clash(Forall(x, Equals(Sum(x, y), z)), Set([z]))
        # w not present — no clash
        @test !has_clash(Forall(x, Equals(Sum(x, y), z)), Set([w]))
        # empty taboo — never clashes
        @test !has_clash(Forall(x, Equals(x, y)), Set{Variable}())
    end

    @testset "Forall — nested quantifiers" begin
        # ∀x. ∀y. x = y — both bound, neither should clash
        nested = Forall(x, Forall(y, Equals(x, y)))
        @test !has_clash(nested, Set([x]))
        @test !has_clash(nested, Set([y]))
        @test !has_clash(nested, Set([x, y]))

        # ∀x. ∀y. x + z = y — z is free
        nested_free = Forall(x, Forall(y, Equals(Sum(x, z), y)))
        @test !has_clash(nested_free, Set([x]))
        @test !has_clash(nested_free, Set([y]))
        @test has_clash(nested_free, Set([z]))

        # ∀x. (∀x. x = y) — inner x shadows outer, y still free
        double_x = Forall(x, Forall(x, Equals(x, y)))
        @test !has_clash(double_x, Set([x]))
        @test has_clash(double_x, Set([y]))
    end

    @testset "Forall — quantifier does not shadow outer free occurrence" begin
        # x appears free in left branch, bound only in right branch
        # ∀y. (x + y = z) — x and z are free, y is bound
        fml = Forall(y, Equals(Sum(x, y), z))
        @test has_clash(fml, Set([x]))
        @test !has_clash(fml, Set([y]))
        @test has_clash(fml, Set([z]))
    end

    @testset "Forall — push/pop correctness (sibling branches)" begin
        # After processing one Forall branch, bound set must be restored.
        # Implies(∀x. x=y,  x=z) — x is free in the right branch
        fml = Implies(Forall(x, Equals(x, y)), Equals(x, z))
        @test has_clash(fml, Set([x]))   # x free in consequent
        @test has_clash(fml, Set([y]))   # y free in antecedent body
        @test has_clash(fml, Set([z]))   # z free in consequent
        # Not(∀x. x=y) — x bound inside Not, not outside
        fml2 = Implies(Not(Forall(x, Equals(x, y))), Equals(x, z))
        @test has_clash(fml2, Set([x]))  # x free in consequent
    end

    # ── Deeply nested terms ──────────────────────────────────────────────────
    @testset "Deep nesting" begin
        # ((x + y) * (z - w)) / (x + 1)
        deep = Division(
            Product(Sum(x, y), Difference(z, w)),
            Sum(x, c1)
        )
        @test has_clash(deep, Set([x]))
        @test has_clash(deep, Set([y]))
        @test has_clash(deep, Set([z]))
        @test has_clash(deep, Set([w]))
        @test !has_clash(deep, Set{Variable}())

        # Deeply nested Forall: ∀x. ∀y. ∀z. x*y*z = w
        deep_forall = Forall(x, Forall(y, Forall(z,
            Equals(Product(Product(x, y), z), w)
        )))
        @test !has_clash(deep_forall, Set([x]))
        @test !has_clash(deep_forall, Set([y]))
        @test !has_clash(deep_forall, Set([z]))
        @test has_clash(deep_forall, Set([w]))
        @test !has_clash(deep_forall, Set([x, y, z]))
        @test has_clash(deep_forall, Set([x, y, z, w]))
    end

    # ── Empty taboo set ──────────────────────────────────────────────────────
    @testset "Empty taboo set never clashes" begin
        empty = Set{Variable}()
        @test !has_clash(x, empty)
        @test !has_clash(Sum(x, y), empty)
        @test !has_clash(Forall(x, Equals(x, y)), empty)
        @test !has_clash(Implies(LessThan(x, y), Equals(z, w)), empty)
    end

    # ── Sequent ──────────────────────────────────────────────────────────────
    @testset "Sequent" begin
        # clash in antecedent
        seq1 = Sequent((Equals(x, c1),), (Equals(y, c2),))
        @test has_clash(seq1, Set([x]))
        @test !has_clash(seq1, Set([z]))

        # clash in consequent
        seq2 = Sequent((Equals(c1, c2),), (Equals(y, c2),))
        @test has_clash(seq2, Set([y]))
        @test !has_clash(seq2, Set([x]))

        # clash in both
        seq3 = Sequent((Equals(x, c1),), (Equals(x, c2),))
        @test has_clash(seq3, Set([x]))

        # no clash anywhere
        seq4 = Sequent((Equals(c1, c2),), (Equals(c2, c1),))
        @test !has_clash(seq4, Set([x, y, z]))

        # empty sequent
        seq5 = Sequent((), ())
        @test !has_clash(seq5, Set([x]))

        # antecedent only
        seq6 = Sequent((LessThan(x, y),), ())
        @test has_clash(seq6, Set([x]))
        @test has_clash(seq6, Set([y]))
        @test !has_clash(seq6, Set([z]))

        # consequent only
        seq7 = Sequent((), (LessThan(x, y),))
        @test has_clash(seq7, Set([x]))
        @test !has_clash(seq7, Set([z]))

        # Forall in sequent — bound variable should not count
        seq8 = Sequent((Forall(x, Equals(x, y)),), (Equals(z, c1),))
        @test !has_clash(seq8, Set([x]))   # x bound in antecedent
        @test has_clash(seq8, Set([y]))   # y free in antecedent
        @test has_clash(seq8, Set([z]))   # z free in consequent

        # multiple antecedents — clash in second
        seq9 = Sequent(
            (Equals(c1, c2), LessThan(x, y)),
            (Equals(c2, c1),)
        )
        @test has_clash(seq9, Set([x]))
        @test has_clash(seq9, Set([y]))
        @test !has_clash(seq9, Set([z]))
    end

    @testset "Substitutions on Terms and Formulas" begin
        # Extensive coverage for mapping FunctionSymbols and PredicateSymbols
        f_sym = FunctionSymbol("f")
        g_sym = FunctionSymbol("g")
        P_sym = PredicateSymbol("P")
        Q_sym = PredicateSymbol("Q")

        f_x = FunctionApplication(f_sym, (x,))
        g_y = FunctionApplication(g_sym, (y,))
        f_c1 = FunctionApplication(f_sym, (c1,))

        P_x = PredicateApplication(P_sym, (x,))
        Q_y = PredicateApplication(Q_sym, (y,))

        @testset "Nullary substitutions" begin
            f_null = FunctionApplication(f_sym, ())
            P_null = PredicateApplication(P_sym, ())

            σ_f = Substitution(f_sym => c2)
            @test substitute(Equals(f_null, y), σ_f) == Equals(c2, y)

            # Since PredicateSymbol -> Formula, let's map P to x < y
            σ_P = Substitution(P_sym => LessThan(x, y))
            @test substitute(Implies(P_null, Q_y), σ_P) == Implies(LessThan(x, y), Q_y)
        end

        @testset "N-ary substitutions with Holes" begin
            # f(x) -> Sum(x, 1) mapping requires Hole(1)
            σ_f_hole = Substitution(f_sym => Sum(Hole(1), c1))

            # f(x) = f(x) + 1  -> x+1 = f(x)+1
            @test substitute(Equals(f_x, z), σ_f_hole) == Equals(Sum(x, c1), z)

            # Nested application f(f(x)) 
            f_f_x = FunctionApplication(f_sym, (f_x,))
            # First f applies: Sum(f(x), 1). Second f applies: Sum(Sum(x, 1), 1)
            @test substitute(Equals(f_f_x, z), σ_f_hole) == Equals(Sum(Sum(x, c1), c1), z)

            # Predicate substitution with holes P(x) -> x < 2
            σ_P_hole = Substitution(P_sym => LessThan(Hole(1), c2))
            @test substitute(P_x, σ_P_hole) == LessThan(x, c2)
        end

        @testset "Mixed Substitutions" begin
            # Combining function and predicate substitutions
            σ_mixed = Substitution(
                f_sym => Product(Hole(1), c2),
                P_sym => Equals(Hole(1), c0)
            )

            # formula: P(f(x))  -> f(x) = 0 -> (x * 2) = 0
            fml = PredicateApplication(P_sym, (f_x,))
            @test substitute(fml, σ_mixed) == Equals(Product(x, c2), c0)
        end

        @testset "Arithmetic Term Substitutions" begin
            σ = Substitution(f_sym => c1)
            f_n = FunctionApplication(f_sym, ())

            @test substitute(Equals(Sum(f_n, x), y), σ) == Equals(Sum(c1, x), y)
            @test substitute(Equals(Difference(f_n, x), y), σ) == Equals(Difference(c1, x), y)
            @test substitute(Equals(Product(f_n, x), y), σ) == Equals(Product(c1, x), y)
            @test substitute(Equals(Division(f_n, x), y), σ) == Equals(Division(c1, x), y)
            @test substitute(Equals(Power(f_n, Constant(2)), y), σ) == Equals(Power(c1, Constant(2)), y)
        end

        @testset "No-op Substitutions" begin
            # Apply empty substitution
            σ_empty = Substitution()
            @test substitute(Equals(f_x, x), σ_empty) == Equals(f_x, x)
            @test substitute(P_x, σ_empty) == P_x

            # Apply substitution for symbols that don't exist in formula
            σ_unused = Substitution(g_sym => c2, Q_sym => Equals(x, y))
            @test substitute(Equals(f_x, x), σ_unused) == Equals(f_x, x)
            @test substitute(P_x, σ_unused) == P_x
        end

        @testset "Clashing Substitutions (Inadmissible)" begin
            # Rule: We cannot substitute an expression containing a free variable 
            # into a context where that variable would become bound (captured).

            # 1. Function substitution capture
            # ∀y. f(x) = y   substituted with [f => y]  ->  ∀y. y = y (Illegal capture of y)
            f_null = FunctionApplication(f_sym, ())
            fml1 = Forall(y, Equals(f_null, y))
            σ_capture_y = Substitution(f_sym => y)
            @test_throws ArgumentError substitute(fml1, σ_capture_y)

            # 2. Predicate substitution capture
            # ∀z. P(x)   substituted with [P => z < x] -> ∀z. z < x (Illegal capture of z)
            P_null = PredicateApplication(P_sym, ())
            fml2 = Forall(z, P_null)
            σ_capture_z = Substitution(P_sym => LessThan(z, x))
            @test_throws ArgumentError substitute(fml2, σ_capture_z)

            # 3. Safe if the variable is replaced by something else, but here we test the clash.
            # Even deep inside arithmetic terms, if a free var is captured, it throws.
            # ∀x. (f(y) + 1) = 2  substituted with [f => x] -> ∀x. (x + 1) = 2 (Illegal capture of x)
            fml3 = Forall(x, Equals(Sum(f_null, c1), c2))
            σ_capture_x = Substitution(f_sym => x)
            @test_throws ArgumentError substitute(fml3, σ_capture_x)

            # 4. Same substitution is safe if it doesn't cross the binder
            fml_safe = Equals(Sum(f_null, c1), c2)
            @test substitute(fml_safe, σ_capture_x) == Equals(Sum(x, c1), c2)

            # 5. Clash through n-ary substitution with holes
            # ∀w. f(x) = 0 substituted with [f(·) -> sum(·, w)] -> ∀w. x + w = 0 (Capture of w)
            fml5 = Forall(w, Equals(f_x, c0))
            σ_capture_w_hole = Substitution(f_sym => Sum(Hole(1), w))
            @test_throws ArgumentError substitute(fml5, σ_capture_w_hole)
        end
    end
end