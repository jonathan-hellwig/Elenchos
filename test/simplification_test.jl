using Elenchos
using Elenchos.Kernel
using Elenchos.Syntax
using Test

@vars x y z w

@testset "Term Normalization" begin
    @testset "Elimination rules" begin
        # Identity
        t, p = normalize(x + 0)
        @test t == x
        t, p = normalize(0 + x)
        @test t == x

        # Zero property
        t, p = normalize(x * 0)
        @test t == Constant(0)
        t, p = normalize(0 * x)
        @test t == Constant(0)

        # Difference elimination
        t, p = normalize(x - y)
        @test t == x + Constant(-1) * y
    end

    @testset "Expansion (Distributivity)" begin
        t, p = normalize(x * (y + z))
        @test t == x * y + x * z
        
        t, p = normalize((y + z) * x)
        @test t == x * y + x * z
        
        # (x + y) * (z + w) - currently simplifies to Horner-like grouping form
        t, p = normalize((x + y) * (z + w))
        @test t == w * x + (w * y + (x + y) * z)
    end

    @testset "Canonicalization and Sorting" begin
        # Associativity and Commutativity
        t, p = normalize(z * y * x)
        @test t == x * (y * z)
        
        t, p = normalize(z + y + x)
        @test t == x + (y + z)

        t, p = normalize((x * y) * z)
        @test t == x * (y * z)
    end

    @testset "Collection of like terms" begin
        t, p = normalize(x + x)
        @test t == Constant(2) * x

        t, p = normalize(Constant(2) * x + Constant(3) * x)
        @test t == Constant(5) * x

        t, p = normalize(x + Constant(2) * x)
        @test t == Constant(3) * x

        t, p = normalize(Constant(3) * x + x)
        @test t == Constant(4) * x

        # Tails
        t, p = normalize(x + x + y)
        @test t == Constant(2) * x + y

        t, p = normalize(Constant(2) * x + (Constant(3) * x + y))
        @test t == Constant(5) * x + y
    end

    @testset "Complex simplifications" begin
        # (x - y) * (x + y) = x^2 - y^2 (Wait, no power operator yet, so x*x - y*y)
        t, p = normalize((x - y) * (x + y))
        @test t == x * x + Constant(-1) * (y * y)

        # (x + y) * (x + y) - currently Horner-like grouped form
        t, p = normalize((x + y) * (x + y))
        @test t == x * x + (Constant(2) * x + y) * y

        # Complex cancellation
        t, p = normalize(x + y * z - x - z * y)
        @test t == Constant(0)
    end

    @testset "Nested simplification" begin
        t, p = normalize(Constant(0) * (x * x + Constant(3) * (y * z) - w))
        @test t == Constant(0)

        # 3(x+2y) - 2(x+3y) = x
        t, p = normalize(Constant(3) * (x + Constant(2) * y) - Constant(2) * (x + Constant(3) * y))
        @test t == x
    end
end
