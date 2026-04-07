using Test
using Elenchos

@vars x y
@preds P Q

A = P(x)
B = Q(y)

@testset "First Locator" begin

    @testset "resolve_cons with First() finds matching formula" begin
        seq = Sequent((A,), (A → B, B))
        loc = resolve_cons(First(), seq, f -> f isa Implies)
        @test loc == Cons(1)
    end

    @testset "resolve_cons with First() finds second match" begin
        seq = Sequent((), (A, B, A → B))
        loc = resolve_cons(First(), seq, f -> f isa Implies)
        @test loc == Cons(3)
    end

    @testset "resolve_cons with First() throws when no match" begin
        seq = Sequent((), (A, B))
        @test_throws TacticFailure resolve_cons(First(), seq, f -> f isa Implies)
    end

    @testset "resolve_cons with Cons(i) validates predicate" begin
        seq = Sequent((), (A → B,))
        loc = resolve_cons(Cons(1), seq, f -> f isa Implies)
        @test loc == Cons(1)
    end

    @testset "resolve_cons with Cons(i) rejects non-matching" begin
        seq = Sequent((), (A, A → B))
        @test_throws TacticFailure resolve_cons(Cons(1), seq, f -> f isa Implies)
    end

    @testset "resolve_cons with Cons(i) rejects out of bounds" begin
        seq = Sequent((), (A,))
        @test_throws TacticFailure resolve_cons(Cons(5), seq, f -> true)
    end

    @testset "resolve_ante with First() finds matching formula" begin
        seq = Sequent((A, A → B), (B,))
        loc = resolve_ante(First(), seq, f -> f isa Implies)
        @test loc == Ante(2)
    end

    @testset "resolve_ante with First() throws when no match" begin
        seq = Sequent((A, B), ())
        @test_throws TacticFailure resolve_ante(First(), seq, f -> f isa Implies)
    end

    @testset "resolve_ante with Ante(i) validates predicate" begin
        seq = Sequent((A → B,), (B,))
        loc = resolve_ante(Ante(1), seq, f -> f isa Implies)
        @test loc == Ante(1)
    end

    @testset "resolve_ante with Ante(i) rejects non-matching" begin
        seq = Sequent((A, A → B), (B,))
        @test_throws TacticFailure resolve_ante(Ante(1), seq, f -> f isa Implies)
    end

    @testset "resolve_ante with Ante(i) rejects out of bounds" begin
        seq = Sequent((A,), ())
        @test_throws TacticFailure resolve_ante(Ante(5), seq, f -> true)
    end

    @testset "nothing causes MethodError (bug signal)" begin
        seq = Sequent((A,), (B,))
        @test_throws MethodError resolve_cons(nothing, seq, f -> true)
        @test_throws MethodError resolve_ante(nothing, seq, f -> true)
    end
end

@testset "Tactics with First locator (interactive defaults)" begin

    @testset "implies_right() uses First() by default" begin
        seq = Sequent((), (A → B,))
        p = start_proof(seq) |> implies_right()
        @test length(p.assumptions) == 1
        @test A in p.assumptions[1].antecedent
    end

    @testset "implies_left() uses First() by default" begin
        seq = Sequent((A → B, A), (B,))
        p = start_proof(seq) |> implies_left()
        @test length(p.assumptions) >= 1
    end

    @testset "not_right() uses First() by default" begin
        seq = Sequent((), (¬A,))
        p = start_proof(seq) |> not_right()
        @test A in p.assumptions[1].antecedent
    end

    @testset "not_left() uses First() by default" begin
        seq = Sequent((¬A,), ())
        p = start_proof(seq) |> not_left()
        @test A in p.assumptions[1].consequent
    end

    @testset "and_left() uses First() by default" begin
        seq = Sequent((A ∧ B,), (A,))
        p = start_proof(seq) |> and_left()
        sub = p.assumptions[1]
        @test A in sub.antecedent
        @test B in sub.antecedent
    end

    @testset "and_right() uses First() by default" begin
        seq = Sequent((A, B), (A ∧ B,))
        p = start_proof(seq) |> and_right()
        @test length(p.assumptions) >= 1
    end

    @testset "or_right() uses First() by default" begin
        seq = Sequent((A,), (A ∨ B,))
        p = start_proof(seq) |> or_right()
        sub = p.assumptions[1]
        @test B in sub.consequent
    end
end

@testset "Tactics with explicit Cons/Ante locator" begin

    @testset "implies_right with explicit Cons(2)" begin
        seq = Sequent((), (A, A → B))
        p = start_proof(seq) |> implies_right(target_idx=Cons(2))
        @test A in p.assumptions[1].antecedent
    end

    @testset "implies_right rejects wrong index" begin
        seq = Sequent((), (A, A → B))
        @test_throws TacticFailure start_proof(seq) |> implies_right(target_idx=Cons(1))
    end

    @testset "not_right with explicit Cons(2)" begin
        seq = Sequent((), (A, ¬B))
        p = start_proof(seq) |> not_right(target_idx=Cons(2))
        @test B in p.assumptions[1].antecedent
    end

    @testset "not_left with explicit Ante(2)" begin
        seq = Sequent((A, ¬B), ())
        p = start_proof(seq) |> not_left(target_idx=Ante(2))
        @test B in p.assumptions[1].consequent
    end
end

@testset "Full proofs with First locator (regression)" begin

    @testset "⊢ A → A" begin
        p = start_proof(A → A) |> implies_right() |> id()
        @test isempty(p.assumptions)
    end

    @testset "A ⊢ ¬¬A" begin
        seq = Sequent((A,), (¬(¬A),))
        p = start_proof(seq) |> not_right() |> not_left() |> id()
        @test isempty(p.assumptions)
    end

    @testset "¬¬A ⊢ A" begin
        seq = Sequent((¬(¬A),), (A,))
        p = start_proof(seq) |> not_left() |> not_right() |> id()
        @test isempty(p.assumptions)
    end

    @testset "A ∧ B ⊢ A" begin
        seq = Sequent((A ∧ B,), (A,))
        p = start_proof(seq) |> and_left() |> id()
        @test isempty(p.assumptions)
    end

    @testset "A, B ⊢ A ∧ B" begin
        seq = Sequent((A, B), (A ∧ B,))
        p = start_proof(seq) |> and_right() |> id() |> id()
        @test isempty(p.assumptions)
    end

    @testset "A ⊢ A ∨ B" begin
        seq = Sequent((A,), (A ∨ B,))
        # or_right() internally does ImpliesRight + NotLeft, giving A ⊢ A, B
        p = start_proof(seq) |> or_right() |> id()
        @test isempty(p.assumptions)
    end

    @testset "B ⊢ A ∨ B" begin
        seq = Sequent((B,), (A ∨ B,))
        p = start_proof(seq) |> or_right() |> id()
        @test isempty(p.assumptions)
    end
end
