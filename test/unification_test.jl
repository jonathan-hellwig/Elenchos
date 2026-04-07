using Test
using Elenchos
using Elenchos.Unification: unify_subterm
using Elenchos.Kernel: is_ground_term
using Elenchos.Unification: match_subterm

@testset "Unification" begin
    x = Variable("x")
    y = Variable("y")
    c1 = Constant(1)
    c2 = Constant(2)

    f = FunctionSymbol("f")
    g = FunctionSymbol("g")
    P = PredicateSymbol("P")

    @testset "is_ground" begin
        @test is_ground_term(c1)
        @test !is_ground_term(x)
        @test is_ground_term(Sum(c1, c2))
        @test !is_ground_term(Sum(x, c1))
        @test !is_ground_term(FunctionApplication(f, (c1, c2)))
        @test !is_ground_term(FunctionApplication(f, (x, c2)))
    end

    @testset "unify terms" begin
        pat_a = FunctionApplication(FunctionSymbol("_a"), ())
        pat_b = FunctionApplication(FunctionSymbol("_b"), ())

        σ = unify(pat_a, c1)
        @test σ !== nothing
        @test substitute(pat_a, σ) == c1

        σ = unify(Sum(pat_a, pat_b), Sum(c1, c2))
        @test σ !== nothing
        @test substitute(Sum(pat_a, pat_b), σ) == Sum(c1, c2)

        # Consistency check for repeated schematic variable
        @test unify(Sum(pat_a, pat_a), Sum(c1, c1)) !== nothing
        @test isnothing(unify(Sum(pat_a, pat_a), Sum(c1, c2)))

        # Type/shape mismatch
        @test isnothing(unify(Sum(pat_a, c1), Product(c1, c1)))
    end

    @testset "unify formulas" begin
        pat_a = FunctionApplication(FunctionSymbol("_a"), ())
        pat_b = FunctionApplication(FunctionSymbol("_b"), ())

        pat_f = LessThan(pat_a, pat_b)
        tgt_f = LessThan(Sum(c1, c2), c2)

        σ = unify(pat_f, tgt_f)
        @test σ !== nothing
        @test substitute(pat_f, σ) == tgt_f

        # Predicate symbol must match
        @test isnothing(unify(PredicateApplication(PredicateSymbol("Q"), (pat_a,)), PredicateApplication(P, (c1,))))
    end

    @testset "match_subterm" begin
        term = Product(Sum(c1, c2), g(c1))

        ctx = match_subterm(Sum(c1, c2), term)
        @test ctx !== nothing
        @test ctx isa Term

        ctx2 = match_subterm(c1, term)
        @test ctx2 !== nothing

        @test isnothing(match_subterm(x, term))
    end

    @testset "unify_subterm and unify_subterm_formula" begin
        pat = Sum(FunctionApplication(FunctionSymbol("_u"), ()), c1)
        term = Product(c2, Sum(c2, c1))

        found = unify_subterm(pat, term)
        @test found !== nothing
        σ, term_ctx = found
        @test substitute(pat, σ) == Sum(c2, c1)
        @test term_ctx isa Term

        fml = Implies(LessThan(Sum(c2, c1), c2), PredicateApplication(P, (x,)))
        found_f = unify_subterm_formula(pat, fml)
        @test found_f !== nothing
        σf, fml_ctx = found_f
        @test substitute(pat, σf) == Sum(c2, c1)
        @test fml_ctx isa Formula
    end

    @testset "find_first_in_sequent" begin
        pat_u = FunctionApplication(FunctionSymbol("_u"), ())
        pat = Sum(pat_u, c1)

        seq = Sequent(
            (LessThan(Sum(c2, c1), c2),),
            (LessThan(c1, c2),)
        )

        site = find_first_in_sequent(seq) do t
            unify(pat, t)
        end

        @test site !== nothing
        @test site.pos isa Ante
        σ = site.data[1]
        @test σ !== nothing
        @test substitute(pat, σ) == Sum(c2, c1)

        # Restrict search to consequent: no match expected there
        site_cons = find_first_in_sequent(
            t -> unify(pat, t),
            seq;
            pos=Cons(1)
        )
        @test isnothing(site_cons)
    end
end
