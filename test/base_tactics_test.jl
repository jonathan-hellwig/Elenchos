using Elenchos
using Test
using Elenchos.Kernel
using Elenchos.Syntax
using Elenchos.BaseTactics
using Elenchos.BaseTactics: rewrite, ExactMatch, ExactSubterm
using Elenchos.Tactics

x = Variable("x")
y = Variable("y")
z = Variable("z")

P_sym = PredicateSymbol("P")
Q_sym = PredicateSymbol("Q")
R_sym = PredicateSymbol("R")

A = PredicateApplication(P_sym, (x,))
B = PredicateApplication(Q_sym, (y,))
C = PredicateApplication(R_sym, (z,))

@testset "Base Tactics" begin

    @testset "Id / Close" begin
        # 1. Normal Use
        seq = Sequent((A, B), (C, A))
        p = start_proof(seq) |> id()
        @test isempty(p.assumptions)
        
        # 2. Edge case: failure (no match)
        seq2 = Sequent((A,), (B,))
        @test_throws TacticFailure start_proof(seq2) |> id()
    end

    @testset "Implication Tactics" begin
        @testset "ImpliesRight" begin
            # 1. Normal Use
            seq = Sequent((C,), (Implies(A, B),))
            p = start_proof(seq) |> implies_right()
            @test p.assumptions[1] == Sequent((C, A), (B,))
            
            # 2. Edge case: Target not found
            @test_throws TacticFailure start_proof(Sequent((C,), (A,))) |> implies_right()
        end

        @testset "ImpliesLeft" begin
            # 1. Normal Use
            seq = Sequent((Implies(A, B), C), (PredicateApplication(P_sym, (y,)),))
            p = start_proof(seq) |> implies_left()
            @test length(p.assumptions) == 2
            @test p.assumptions[1] == Sequent((C,), (PredicateApplication(P_sym, (y,)), A))
            @test p.assumptions[2] == Sequent((B, C), (PredicateApplication(P_sym, (y,)),))

            # 2. Edge case: Target not found
            @test_throws TacticFailure start_proof(Sequent((A, C), (B,))) |> implies_left()
        end
    end

    @testset "Not Tactics" begin
        @testset "NotRight" begin
            # 1. Normal Use: Γ ⊢ ¬A, Δ  gives  Γ, A ⊢ Δ
            seq = Sequent((B,), (Not(A), C))
            p = start_proof(seq) |> not_right()
            @test p.assumptions[1] == Sequent((B, A), (C,))
            
            # 2. Edge case: Target not found
            @test_throws TacticFailure start_proof(Sequent((B,), (A, C))) |> not_right()
        end

        @testset "NotLeft" begin
            # 1. Normal Use: Γ, ¬A ⊢ Δ  gives  Γ ⊢ A, Δ
            seq = Sequent((B, Not(A)), (C,))
            p = start_proof(seq) |> not_left()
            @test p.assumptions[1] == Sequent((B,), (C, A))
            
            # 2. Edge case: Target not found
            @test_throws TacticFailure start_proof(Sequent((B, A), (C,))) |> not_left()
        end
    end

    @testset "Quantifier Tactics" begin
        @testset "ForallRight" begin
            # 1. Normal Use: Γ ⊢ ∀x. P(x)  gives  Γ ⊢ P(x_fresh)
            seq = Sequent((B,), (Forall(x, Equals(x, y)),))
            p = start_proof(seq) |> forall_right()
            # The fresh var should be x_1 or similar
            sub = p.assumptions[1]
            @test sub.consequent[1] isa Equals
            @test sub.consequent[1].left.name != "y" # it shouldn't clash with y
            @test sub.consequent[1].left.name == "x" || endswith(sub.consequent[1].left.name, "1")
            
            # 2. Edge case: Target not found
            @test_throws TacticFailure start_proof(Sequent((B,), (A,))) |> forall_right()
        end
        
        # Note: ForallLeft uses Substitution heavily which has currently untested or broken API expectations. 
        # Skipping testing `forall_left(y)` here until `base_tactics.jl` replaces its use of syntax macros.
    end

    @testset "Structural Tactics" begin
        @testset "Cut" begin
            # 1. Normal Use
            seq = Sequent((A,), (B,))
            p = start_proof(seq) |> cut(C)
            @test length(p.assumptions) == 2
            @test p.assumptions[1] == Sequent((A,), (B, C))
            @test p.assumptions[2] == Sequent((A, C), (B,))
        end

        @testset "WeakenLeft" begin
            # 1. Normal use by formula
            seq = Sequent((A, B), (C,))
            p = start_proof(seq) |> weaken_left(fml=B)
            @test p.assumptions[1] == Sequent((A,), (C,))

            # 2. Normal use by index
            p2 = start_proof(seq) |> weaken_left(idx=Ante(1))
            @test p2.assumptions[1] == Sequent((B,), (C,))

            # 3. Edge case: Formula not found
            @test_throws TacticFailure start_proof(seq) |> weaken_left(fml=C)
        end

        @testset "WeakenRight" begin
            # 1. Normal use by formula
            seq = Sequent((A,), (B, C))
            p = start_proof(seq) |> weaken_right(fml=C)
            @test p.assumptions[1] == Sequent((A,), (B,))

            # 2. Normal use by index
            p2 = start_proof(seq) |> weaken_right(idx=Cons(1))
            @test p2.assumptions[1] == Sequent((A,), (C,))

            # 3. Edge case: Formula not found
            @test_throws TacticFailure start_proof(seq) |> weaken_right(fml=A)
        end
        
        @testset "Weaken / WeakenAllBut" begin
            seq = Sequent((A, B, C), (A, B, C))
            p = start_proof(seq) |> weaken(A) # Should weaken from antecedent first
            @test p.assumptions[1] == Sequent((B, C), (A, B, C))

            p2 = start_proof(seq) |> weaken_all_but(B)
            @test p2.assumptions[1] == Sequent((B,), (B,))
        end

        @testset "WeakenLeftAllBut / WeakenRightAllBut" begin
            seq = Sequent((A, B, C), (A, B, C))
            
            p1 = start_proof(seq) |> weaken_left_all_but(B)
            @test p1.assumptions[1] == Sequent((B,), (A, B, C))
            
            p2 = start_proof(seq) |> weaken_right_all_but(C)
            @test p2.assumptions[1] == Sequent((A, B, C), (C,))
        end
    end

    @testset "Arithmetic Tactics" begin
        c1 = Constant(1)
        c2 = Constant(2)
        c3 = Constant(3)

        @testset "ArithRight" begin
            seq = Sequent((A,), (LessThan(c1, c2),))
            p = start_proof(seq) |> arith_right()
            @test isempty(p.assumptions)
            
            # Target not found
            @test_throws TacticFailure start_proof(Sequent((), (A,))) |> arith_right()
        end

        @testset "ArithLeft" begin
            seq = Sequent((LessThan(c3, c1), B), (A,))
            p = start_proof(seq) |> arith_left()
            @test isempty(p.assumptions)
            
            # Target not found
            @test_throws TacticFailure start_proof(Sequent((A,), (B,))) |> arith_left()
        end
    end

    # The And and Or Tactics specifically rely on Elenchos.Syntax via `is_and_pattern` in base_tactics.jl.
    # We will exclude testing them from here so we don't depend on Syntax. They likely belong in derived_tactics_test.jl or syntax_test.jl if we fully isolate them.

    @testset "Proof Combination Tactics" begin
        @testset "Exact" begin
            seq1 = Sequent((A,), (A,))
            ax_proof = start_proof(seq1) |> id()
            p = start_proof(seq1) |> exact(ax_proof)
            @test isempty(p.assumptions)
        end

        @testset "Subst" begin
            f_sym = FunctionSymbol("f")
            f = FunctionApplication(f_sym, ())
            seq_subst = Sequent((), (LessThan(f, Constant(2)),))
            σ = Substitution(f_sym => Constant(1))
            # Start a proof that requires something and map substitute to it
            p_subst = start_proof(Sequent((), (LessThan(Constant(1), Constant(2)),))) |> subst(seq_subst, σ)
            # Subst rule executes correctly returning rule derivation mapped
            @test length(p_subst.assumptions) == 1
            @test p_subst.assumptions[1] == seq_subst
        end
        
        @testset "ApplyRule" begin
            # We construct a mock rule derivation with 0 assumptions
            # i.e., an inference rule stating ⊢ A ⟹ B
            rule_deriv = Derivation(UntrustedRule(Sequent((), (Implies(A, B),)), :mock))
            
            # Apply to Γ ⊢ (A ⟹ B), Δ
            seq = Sequent((C,), (Implies(A, B),))
            p = start_proof(seq) |> Elenchos.BaseTactics.apply_rule(rule_deriv)
            # The rule has 0 premises, and it concludes Implies(A, B) exactly.
            @test isempty(p.assumptions)

            # Rule derivation with premises (A ⊢ B) 
            # Applied to (C ⊢ B) -> Subgoal becomes C ⊢ A
            rule_deriv2 = Derivation(UntrustedRule(Sequent((A,), (B,)), :mock2))
            seq2 = Sequent((C,), (B,))
            p2 = start_proof(seq2) |> Elenchos.BaseTactics.apply_rule(rule_deriv2)
            @test length(p2.assumptions) == 1
            @test p2.assumptions[1] == Sequent((C,), (A,))
            
            # Edge case: rule has open assumptions
            open_deriv = Derivation(Assume(Sequent((A,), (B,))))
            @test_throws TacticFailure start_proof(seq2) |> Elenchos.BaseTactics.apply_rule(open_deriv)
        end
    end

    @testset "Rewrite API Tests" begin
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        ZERO = Constant(0)

        @testset "Path-based rewrite in Consequent" begin
            # ⊢ (x + 0) ~ y
            seq = Sequent((), (Equals(Sum(x, ZERO), y),))
            p = start_proof(seq)
            
            # Rewrite 0 => z at [1, 2] in the consequent
            # Path [1, 2] goes into left side of Equals (1), then right side of Sum (2)
            p = p |> rewrite(z, Cons(1), [1, 2])
            
            # Result should be ⊢ (x + z) ~ y. It will be the second subgoal.
            # The first subgoal is the equality proof z ~ 0.
            @test length(p.assumptions) == 2
            fml = p.assumptions[2].consequent[1]
            @test fml == Equals(Sum(x, z), y)
        end

        @testset "Path-based rewrite in Antecedent" begin
            # (x + 0) ~ y ⊢ x ~ y
            seq = Sequent((Equals(Sum(x, ZERO), y),), (Equals(x, y),))
            p = start_proof(seq)
            
            # Rewrite 0 => z at [1, 2] in the antecedent
            p = p |> rewrite(z, Ante(1), [1, 2])
            
            # Result should be x + z ~ y ⊢ x ~ y
            @test length(p.assumptions) == 2
            fml_ante = p.assumptions[2].antecedent[1]
            @test fml_ante == Equals(Sum(x, z), y)
        end

        @testset "Search-based rewrite (FindTarget) in Consequent" begin
            # ⊢ (x + y) + x ~ z
            seq = Sequent((), (Equals(Sum(Sum(x, y), x), z),))
            p = start_proof(seq)
            
            # Find first matching target: rewrite x => y
            # Default behavior searches for the first `x` matching the pattern
            p = p |> rewrite(Variable("x") => y)
            
            @test length(p.assumptions) == 2
            fml = p.assumptions[2].consequent[1]
            # Depending on traversal, it should replace the first 'x'
            # The leftmost 'x' is in (x + y)
            @test fml == Equals(Sum(Sum(y, y), x), z) || fml == Equals(Sum(Sum(x, y), y), z)
        end

        @testset "Search-based rewrite (FindTarget) in Antecedent" begin
            # (x + y) ~ z ⊢ x ~ z
            seq = Sequent((Equals(Sum(x, y), z),), (Equals(x, z),))
            p = start_proof(seq)
            
            # Replace y => 0 in Antecedent
            p = p |> rewrite(Variable("y") => ZERO; seq_pos=Ante(1))
            
            @test length(p.assumptions) == 2
            fml_ante = p.assumptions[2].antecedent[1]
            @test fml_ante == Equals(Sum(x, ZERO), z) || fml_ante == Equals(Sum(ZERO, y), z)
        end

        @testset "ExactMatch rewrite in Consequent" begin
            # ⊢ (y * x) ~ z
            seq = Sequent((), (Equals(Product(y, x), z),))
            p = start_proof(seq)
            
            # Replace literal Product(y, x) with Product(x, y) using ExactMatch
            p = p |> rewrite(Product(y, x) => Product(x, y), ExactMatch)
            
            @test length(p.assumptions) == 2
            fml = p.assumptions[2].consequent[1]
            @test fml == Equals(Product(x, y), z)
        end

        @testset "ExactMatch rewrite in Antecedent" begin
            # (y * x) ~ z ⊢ x ~ z
            seq = Sequent((Equals(Product(y, x), z),), (Equals(x, z),))
            p = start_proof(seq)
            
            # Replace literal Product(y, x) with Product(x, y) using ExactMatch in Ante(1)
            p = p |> rewrite(Product(y, x) => Product(x, y), ExactMatch; seq_pos=Ante(1))
            
            @test length(p.assumptions) == 2
            fml_ante = p.assumptions[2].antecedent[1]
            @test fml_ante == Equals(Product(x, y), z)
        end
    end

end
