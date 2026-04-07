# ═══════════════════════════════════════════════════════════════════════════════
#                Tests for Ring Normalization Tactics
#
#   term_lt         — total order on terms
# ═══════════════════════════════════════════════════════════════════════════════

using Elenchos
using Elenchos.Kernel
using Elenchos.Syntax
using Elenchos.BaseTactics: start_proof
using Elenchos.DerivedTactics: refl
using Elenchos.Strategy: solve_dfs, Then, Repeat
using Test

x = Variable("x")
y = Variable("y")
z = Variable("z")
w = Variable("w")

# ─────────────────────────────────────────────────────────────────────────────
#                         term_lt ordering
# ─────────────────────────────────────────────────────────────────────────────

@testset "term_lt" begin
    @testset "constants before variables" begin
        @test term_lt(ZERO, x)
        @test term_lt(ONE, x)
        @test !term_lt(x, ZERO)
    end

    @testset "constants by value" begin
        @test term_lt(ZERO, ONE)
        @test !term_lt(ONE, ZERO)
        @test !term_lt(ONE, ONE)
    end

    @testset "variables by name" begin
        @test term_lt(x, y)
        @test term_lt(x, z)
        @test !term_lt(y, x)
        @test !term_lt(x, x)
    end

    @testset "compound terms" begin
        @test term_lt(x, x + y)           # variable < sum
        @test term_lt(x + y, x + z)       # lexicographic
        @test !term_lt(x + z, x + y)
    end
end

# ─────────────────────────────────────────────────────────────────────────────
#                         arith strategy
# ─────────────────────────────────────────────────────────────────────────────


@testset "arith" begin
    @testset "simple: 1+1 = 2" begin
        p = start_proof(Equals(Constant(1) + Constant(1), Constant(2)))
        p2 = p |> arith()
        @test isempty(p2.assumptions)
    end

    @testset "compound: (2+3)*2 = 10" begin
        p = start_proof(Equals(Product(Constant(2) + Constant(3), Constant(2)), Constant(10)))
        p2 = p |> arith()
        @test isempty(p2.assumptions)
    end

    @testset "negative: 2+(-1) = 1" begin
        p = start_proof(Equals(Constant(2) + Constant(-1), Constant(1)))
        p2 = p |> arith()
        @test isempty(p2.assumptions)
    end

    @testset "zero: 0 = 0" begin
        p = start_proof(Equals(Constant(0), Constant(0)))
        p2 = p |> arith()
        @test isempty(p2.assumptions)
    end
end

# ─────────────────────────────────────────────────────────────────────────────
#                         ring_norm strategy
# ─────────────────────────────────────────────────────────────────────────────


@testset "ring_norm" begin
    @testset "commutativity: y+x = x+y" begin
        p = start_proof(y + x ~ x + y) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "distributivity + collection" begin
        p = start_proof(x * (y + z) - x ~ x * y + x * z - x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "constant folding: 2x+3x = 5x" begin
        p = start_proof(2 * x + 3 * x ~ 5 * x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "like-term collection: x+x = 2x" begin
        p = start_proof(x + x ~ 2 * x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "subtraction cancellation: x-x = 0" begin
        p = start_proof(x - x ~ 0) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "multi-variable sorting" begin
        p = start_proof(z + y + x ~ x + (y + z)) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "product sorting: z*y*x = x*(y*z)" begin
        p = start_proof(z * y * x ~ x * (y * z)) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "full polynomial" begin
        p = start_proof(x * (1 + 1) * y * 2 + x + x ~ 4 * (x * y) + 2 * x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "zero annihilation: 0*x+y = y" begin
        p = start_proof(0 * x + y ~ y) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "multiplicative identity: 1*x = x" begin
        p = start_proof(1 * x ~ x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

        @testset "FOIL distribution: (x+y)*(z+w) = x*z + x*w + y*z + y*w" begin
        # Checks that nested sums distribute accurately
        p = start_proof((x + y) * (z + w) ~ x * z + x * w + y * z + y * w) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "binomial expansion: (x+y)*(x+y) = x*x + 2*x*y + y*y" begin
        # Checks that identical collected cross-terms (xy and yx) compute to 2xy
        p = start_proof((x + y) * (x + y) ~ x * x + 2 * (x * y) + y * y) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "difference of squares: (x-y)*(x+y) = x*x - y*y" begin
        # Checks exact cancellation of the inner xy and -yx terms
        p = start_proof((x - y) * (x + y) ~ x * x - y * y) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "complex cancellation to zero" begin
        # Commutative term matching subtraction (xy vs yx)
        p = start_proof(x + y * z - x - z * y ~ 0) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "negative sign distribution: -1*(x-y) = y-x" begin
        p = start_proof((-1) * (x - y) ~ y - x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "deeply nested additive associativity/commutativity" begin
        p = start_proof(x + (y + (z + w)) ~ (((w + y) + x) + z)) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "deeply nested multiplicative associativity/commutativity" begin
        p = start_proof(x * (y * (z * w)) ~ (((w * y) * x) * z)) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end

    @testset "nested zero annihilation" begin
        # 0 annihilating a massively nested multi-term polynomial
        p = start_proof(0 * (x * x + 3 * (y * z) - w) ~ 0) |> ring_norm()
        @test isempty(p.assumptions)
    end

    @testset "double distribution and coefficient math" begin
        # 3(x+2y) - 2(x+3y) = 3x + 6y - 2x - 6y = x
        p = start_proof(3 * (x + 2 * y) - 2 * (x + 3 * y) ~ x) |> ring_norm() |> refl()
        @test isempty(p.assumptions)
    end
end