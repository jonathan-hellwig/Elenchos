using Test
using Elenchos
using Elenchos.Kernel

@testset "Kernel Rules & Derivations" begin
    x = Variable("x")
    y = Variable("y")
    z = Variable("z")
    A = Equals(x, y)
    B = LessThan(x, y)
    C = LessThan(y, z)
    c0 = Constant(0)
    c1 = Constant(1)
    c2 = Constant(2)

    @testset "Basic Construction Rules" begin
        @testset "Assume" begin
            # 1. Normal use
            seq1 = Sequent((A,), (B,))
            deriv1 = Derivation(Assume(seq1))
            @test deriv1.conclusion == seq1
            @test length(deriv1.assumptions) == 1

            # 2. Edge case: empty
            seq2 = Sequent((), ())
            deriv2 = Derivation(Assume(seq2))
            @test deriv2.assumptions[1] == seq2

            # 3. Edge case: big sequent
            seq3 = Sequent((A, B, C), (A, B, C))
            deriv3 = Derivation(Assume(seq3))
            @test deriv3.assumptions[1] == seq3
        end

        @testset "AxiomRule" begin
            # 1. Normal use with a built-in kernel axiom
            deriv1 = Derivation(AxiomRule(AX_EQ_REFL))
            @test isempty(deriv1.assumptions)
            @test deriv1.conclusion == Sequent((), (AX_EQ_REFL.formula,))

            # 2. Reject non-kernel axioms
            @test_throws ArgumentError AxiomRule(KernelAxiom(Implies(A, A)))

            # 3. Reject arbitrary quantified formulas as axioms
            @test_throws ArgumentError AxiomRule(KernelAxiom(Forall(x, A)))
        end

        @testset "UntrustedRule" begin
            # 1. Normal use
            seq = Sequent((A,), (B,))
            deriv1 = Derivation(UntrustedRule(seq, :oracle))
            @test isempty(deriv1.assumptions)
            @test deriv1.conclusion == seq
            @test :oracle in deriv1.tools

            # 2. Edge case: empty toolkit
            deriv2 = Derivation(UntrustedRule(Sequent((), ()), :cheat))
            @test :cheat in deriv2.tools
            @test deriv2.conclusion == Sequent((),())

            # 3. Edge case: tracking tool from rule creation
            r3 = UntrustedRule(seq, :smt)
            deriv3 = Derivation(r3)
            @test deriv3.rule == r3
        end
    end

    @testset "Right Rules" begin
        @testset "ImpliesRightRule" begin
            # 1. Normal use
            seq1 = Sequent((), (Implies(A, B),))
            r1 = ImpliesRightRule(seq1, Cons(1), Ante(1))
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((A,), (B,))

            # 2. Edge case: Wrong target type
            seq2 = Sequent((), (A,))
            @test_throws ArgumentError ImpliesRightRule(seq2, Cons(1), Ante(1))

            # 3. Edge case: Out of bounds
            @test_throws BoundsError ImpliesRightRule(seq1, Cons(2), Ante(1))
            @test_throws BoundsError ImpliesRightRule(seq1, Cons(1), Ante(2))
        end

        @testset "NotRightRule" begin
            # 1. Normal use
            seq1 = Sequent((), (Not(A),))
            r1 = NotRightRule(seq1, Cons(1), Ante(1))
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((A,), ())

            # 2. Edge case: Not finding Not
            @test_throws ArgumentError NotRightRule(Sequent((), (A,)), Cons(1), Ante(1))

            # 3. Edge case: Preserve context
            seq3 = Sequent((B,), (Not(A), C))
            r3 = NotRightRule(seq3, Cons(1), Ante(2))
            deriv3 = Derivation(r3)
            @test deriv3.assumptions[1] == Sequent((B, A), (C,))
        end

        @testset "ForallRightRule" begin
            # 1. Normal use: fresh variable correctly substitutes
            seq1 = Sequent((B,), (Forall(x, Equals(y, x)),))
            r1 = ForallRightRule(seq1, Cons(1), z) # z is fresh
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((B,), (Equals(y, z),))

            # 2. Edge case: NOT fresh variable
            @test_throws ArgumentError ForallRightRule(seq1, Cons(1), y) # y is in context

            # 3. Edge case: out of bounds or not Forall
            @test_throws ArgumentError ForallRightRule(Sequent((), (A,)), Cons(1), z)
            @test_throws BoundsError ForallRightRule(seq1, Cons(2), z)
        end
    end

    @testset "Left Rules" begin
        @testset "ImpliesLeftRule" begin
            # 1. Normal use
            seq1 = Sequent((Implies(A, B),), (C,))
            r1 = ImpliesLeftRule(seq1, Ante(1), Cons(1))
            deriv1 = Derivation(r1)
            @test length(deriv1.assumptions) == 2
            @test deriv1.assumptions[1] == Sequent((), (A, C)) # Show A
            @test deriv1.assumptions[2] == Sequent((B,), (C,)) # Assuming B, show C

            # 2. Edge case: Wrong target
            @test_throws ArgumentError ImpliesLeftRule(Sequent((A,), ()), Ante(1), Cons(1))

            # 3. Edge case: bounds
            @test_throws BoundsError ImpliesLeftRule(seq1, Ante(2), Cons(1))
        end

        @testset "NotLeftRule" begin
            # 1. Normal use
            seq1 = Sequent((Not(A),), (C,))
            r1 = NotLeftRule(seq1, Ante(1), Cons(1))
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((), (A, C))

            # 2. Edge case: Wrong type
            @test_throws ArgumentError NotLeftRule(Sequent((A,), ()), Ante(1), Cons(1))

            # 3. Edge case: context preservation
            seq3 = Sequent((B, Not(A)), (C,))
            r3 = NotLeftRule(seq3, Ante(2), Cons(2))
            deriv3 = Derivation(r3)
            @test deriv3.assumptions[1] == Sequent((B,), (C, A))
        end
    end

    @testset "Structural Rules" begin
        @testset "CloseRule" begin
            # 1. Normal use
            seq1 = Sequent((A, B), (C, A))
            r1 = CloseRule(seq1, Ante(1), Cons(2))
            deriv1 = Derivation(r1)
            @test isempty(deriv1.assumptions)

            # 2. Edge case: Mismatch formulas
            @test_throws ArgumentError CloseRule(seq1, Ante(1), Cons(1)) # A != C

            # 3. Edge case: Out of bounds
            @test_throws BoundsError CloseRule(seq1, Ante(3), Cons(1))
        end

        @testset "SubstitutionRule" begin
            # 1. Normal use
            seq1 = Sequent((LessThan(x, c1),), (Equals(y, z),))
            subst = Substitution(Dict{FunctionSymbol,Term}(FunctionSymbol("f") => c2)) # noop
            r1 = SubstitutionRule(seq1, subst)
            deriv1 = Derivation(r1)
            @test length(deriv1.assumptions) == 1
            @test deriv1.conclusion.antecedent == seq1.antecedent
            
            # 2. Edge case (actual substitution)
            f_sym = FunctionSymbol("f")
            f_app = FunctionApplication(f_sym, ())
            seq2 = Sequent((LessThan(f_app, c1),), ())
            subst2 = Substitution(f_sym => c2)
            r2 = SubstitutionRule(seq2, subst2)
            deriv2 = Derivation(r2)
            @test deriv2.conclusion == Sequent((LessThan(c2, c1),), ())

            # 3. Edge case: empty sequent
            seq_empty = Sequent((), ())
            deriv3 = Derivation(SubstitutionRule(seq_empty, subst2))
            @test deriv3.conclusion == seq_empty
        end

        @testset "WeakeningLeftRule" begin
            # 1. Normal
            seq1 = Sequent((A, B), (C,))
            r1 = WeakeningLeftRule(seq1, Ante(1))
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((B,), (C,))

            # 2. Edge case: out of bounds
            @test_throws BoundsError WeakeningLeftRule(seq1, Ante(3))

            # 3. Edge case: weakening only antecedent leaves it empty
            seq3 = Sequent((A,), ())
            r3 = WeakeningLeftRule(seq3, Ante(1))
            deriv3 = Derivation(r3)
            @test deriv3.assumptions[1] == Sequent((), ())
        end

        @testset "WeakeningRightRule" begin
            # 1. Normal
            seq1 = Sequent((A,), (B, C))
            r1 = WeakeningRightRule(seq1, Cons(1))
            deriv1 = Derivation(r1)
            @test deriv1.assumptions[1] == Sequent((A,), (C,))

            # 2. Edge case: bounds
            @test_throws BoundsError WeakeningRightRule(seq1, Cons(3))

            # 3. Edge case: empty right
            seq3 = Sequent((), (A,))
            r3 = WeakeningRightRule(seq3, Cons(1))
            deriv3 = Derivation(r3)
            @test deriv3.assumptions[1] == Sequent((), ())
        end

        @testset "CutRule" begin
            # 1. Normal use
            seq1 = Sequent((A,), (B,))
            r1 = CutRule(seq1, C, Cons(2), Ante(2))
            deriv1 = Derivation(r1)
            @test length(deriv1.assumptions) == 2
            @test deriv1.assumptions[1] == Sequent((A,), (B, C))
            @test deriv1.assumptions[2] == Sequent((A, C), (B,))

            # 2. Edge case: Insert bounds
            @test_throws BoundsError CutRule(seq1, C, Cons(3), Ante(1))
            @test_throws BoundsError CutRule(seq1, C, Cons(1), Ante(3))

            # 3. Edge case: cut on empty sequent
            seq3 = Sequent((), ())
            r3 = CutRule(seq3, A, Cons(1), Ante(1))
            deriv3 = Derivation(r3)
            @test deriv3.assumptions[1] == Sequent((), (A,))
            @test deriv3.assumptions[2] == Sequent((A,), ())
        end
    end

    @testset "Ground Evaluators" begin
        @testset "is_ground_term" begin
            # 1. Normal Use: pure constants and their arithmetic
            @test is_ground_term(c1)
            @test is_ground_term(Sum(c1, c2))
            @test is_ground_term(Power(c2, Constant(3)))

            # 2. Edge case: variables and holes are NOT ground
            @test !is_ground_term(x)
            @test !is_ground_term(Hole(1))

            # 3. Edge case: arithmetic and functions containing non-ground propagates false
            @test !is_ground_term(Sum(x, c1))
            f_sym = FunctionSymbol("f")
            @test !is_ground_term(FunctionApplication(f_sym, (c1,)))
        end

        @testset "evaluate_ground_term" begin
            # 1. Normal Use: arithmetic evaluation
            @test evaluate_ground_term(c1) == 1
            @test evaluate_ground_term(Sum(c1, c2)) == 3
            @test evaluate_ground_term(Product(c2, Constant(3))) == 6
            @test evaluate_ground_term(Difference(Constant(5), c2)) == 3
            @test evaluate_ground_term(Division(Constant(6), c2)) == 3

            # 2. Edge case: Power and deeply nested evaluation
            @test evaluate_ground_term(Power(c2, Constant(3))) == 8
            @test evaluate_ground_term(Sum(c1, Sum(c1, c1))) == 3
            @test evaluate_ground_term(Product(c2, Sum(c1, c2))) == 6

            # 3. Edge case: evaluating non-ground term throws error
            @test_throws ErrorException evaluate_ground_term(x)
            @test_throws ErrorException evaluate_ground_term(Hole(1))
            @test_throws ErrorException evaluate_ground_term(Sum(x, c1))
        end

        @testset "GroundInequalityRightRule" begin
            # 1. Normal Use: 1 < 2
            r1 = GroundInequalityRightRule(c1, c2)
            d1 = Derivation(r1)
            @test isempty(d1.assumptions)
            @test d1.conclusion == Sequent((), (LessThan(c1, c2),))

            # 2. Edge case: Wrong inequality
            @test_throws ArgumentError GroundInequalityRightRule(c2, c1)
            @test_throws ArgumentError GroundInequalityRightRule(c1, c1)

            # 3. Edge case: Not ground
            @test_throws ArgumentError GroundInequalityRightRule(x, c2)
        end

        @testset "GroundInequalityLeftRule" begin
            # 1. Normal Use: 2 < 1 ⊢ false
            r1 = GroundInequalityLeftRule(c2, c1)
            d1 = Derivation(r1)
            @test isempty(d1.assumptions)
            @test d1.conclusion == Sequent((LessThan(c2, c1),), ())

            # 2. Edge case: True inequality on left doesn't close proof
            @test_throws ArgumentError GroundInequalityLeftRule(c1, c2)

            # 3. Edge case: Not ground
            @test_throws ArgumentError GroundInequalityLeftRule(c2, x)
        end
    end

    @testset "Proof Combination" begin
        @testset "ApplySubproof" begin
            seq = Sequent((A,), (B,))
            main_deriv = Derivation(Assume(seq))
            sub_deriv = Derivation(UntrustedRule(seq, :oracle))

            # 1. Normal Use
            d1 = Derivation(main_deriv, 1, sub_deriv)
            @test isempty(d1.assumptions)
            @test d1.conclusion == seq
            @test :oracle in d1.tools

            # 2. Edge case: Invalid subgoal idx
            @test_throws BoundsError Derivation(main_deriv, 2, sub_deriv)

            # 3. Edge case: Mismatched conclusion
            bad_sub = Derivation(UntrustedRule(Sequent((), ()), :cheat))
            @test_throws ArgumentError Derivation(main_deriv, 1, bad_sub)
        end
    end
end
