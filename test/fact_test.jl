using Test
using Elenchos
using Elenchos.Kernel
using Elenchos.Syntax
using Elenchos.BaseTactics
using Elenchos.DerivedTactics

@testset "Proof-Carrying Fact Algebra" begin
    @vars x y z w
    @preds A B

    @testset "EqualityFact" begin
        f1 = Fact(x ~ y)
        @test f1 isa EqualityFact
        @test f1.left == x
        @test f1.right == y

        @testset "Constructors & Error Handling" begin
            # Invalid constructor cases
            open_proof = start_proof((x ~ z) → (x ~ y)) |> implies_right()
            @test_throws ErrorException EqualityFact(x, y, open_proof) # Proof is not closed
            
            wrong_target_proof = start_proof((x ~ w) ⊢ (x ~ w)) |> id()
            @test_throws ErrorException EqualityFact(x, y, wrong_target_proof) # conclusion mismatch
        end

        @testset "Addition" begin
            f2 = Fact(z ~ w)
            f_sum = f1 + f2
            @test f_sum.left == x + z
            @test f_sum.right == y + w
            @test isempty(f_sum.proof.assumptions)
            @test length(f_sum.proof.conclusion.antecedent) == 2
            @test f_sum.proof.conclusion.antecedent[1] == (x ~ y)
            @test f_sum.proof.conclusion.antecedent[2] == (z ~ w)
        end

        @testset "Scaling" begin
            f_scaled = 2 * f1
            @test f_scaled.left == 2 * x
            @test f_scaled.right == 2 * y
            @test f_scaled.proof.conclusion.antecedent[1] == (x ~ y)

            f_scaled_right = f1 * 3
            @test f_scaled_right.left == x * 3
            @test f_scaled_right.right == y * 3
        end

        @testset "Subtraction & Negation" begin
            f2 = Fact(z ~ w)
            f_diff = f1 - f2
            @test f_diff.left == x - z
            @test f_diff.right == y - w

            f_neg = -f1
            @test f_neg.left == -1 * x
            @test f_neg.right == -1 * y
        end
    end

    @testset "InequalityFact" begin
        f1 = Fact(x ≤ y)
        @test f1 isa InequalityFact
        @test f1.left == x
        @test f1.right == y

        @testset "Constructors & Error Handling" begin
            @test_throws ErrorException InequalityFact(x ~ y) # Must be ≤ pattern
            open_proof = start_proof((x ≤ y) → (x ≤ z)) |> implies_right()
            @test_throws ErrorException InequalityFact(x, y, open_proof) # Must be closed
        end

        @testset "Addition" begin
            f2 = Fact(z ≤ w)
            f_sum = f1 + f2
            @test f_sum.left == x + z
            @test f_sum.right == y + w

            f_const_right = f1 + 5
            @test f_const_right.left == x + 5
            @test f_const_right.right == y + 5

            f_const_left = 5 + f1
            @test f_const_left.left == 5 + x
            @test f_const_left.right == 5 + y
        end

        @testset "Positive Scaling" begin
            f_pos = 2 * f1
            @test f_pos.left == 2 * x
            @test f_pos.right == 2 * y
            @test isempty(f_pos.proof.assumptions)
        end

        @testset "Negative Scaling (Flipping)" begin
            f_neg = -1 * f1
            # x ≤ y  * -1  =>  -1*y ≤ -1*x
            @test f_neg.left == -1 * y
            @test f_neg.right == -1 * x
            @test isempty(f_neg.proof.assumptions)

            # Verify it works with right-multiply too
            f_neg_right = f1 * -2
            @test f_neg_right.left == y * -2
            @test f_neg_right.right == x * -2
            @test isempty(f_neg_right.proof.assumptions)
        end

        @testset "Subtraction (Cross-Subtraction)" begin
            f1 = Fact(x ≤ y)
            f2 = Fact(z ≤ w)
            # (x ≤ y) - (z ≤ w) => (x - w ≤ y - z)
            f_diff = f1 - f2
            @test f_diff.left == x - w
            @test f_diff.right == y - z
            @test isempty(f_diff.proof.assumptions)
            
            # Subtraction by constant c - (x <= y) => c - y <= c - x
            f_c_sub = 5 - f1
            @test f_c_sub.left == 5 - y
            @test f_c_sub.right == 5 - x
        end
    end

    @testset "Derivation Extraction (ante)" begin
        p = start_proof((x ~ z, x ≤ y, y ≤ z) ⊢ (0 ≤ z - x))
        
        # Test extracting single facts
        f_eq = ante(p, 1)
        @test f_eq isa EqualityFact
        @test f_eq.left == x
        @test f_eq.right == z

        f_leq = ante(p, 2)
        @test f_leq isa InequalityFact
        @test f_leq.left == x
        @test f_leq.right == y
    end
end