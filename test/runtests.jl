using Test
using Elenchos

@testset "Elenchos Tests" begin
    @testset "Kernel Syntax & Equality" begin
        include("kernel_syntax_test.jl")
    end

    @testset "Kernel Substitution & Clash" begin
        include("kernel_substitution_test.jl")
    end

    @testset "Kernel Rules & Proof State" begin
        include("kernel_rules_test.jl")
    end

    @testset "Base Tactics" begin
        include("base_tactics_test.jl")
    end

    @testset "Serialization" begin
        include("serialization_test.jl")
    end

    @testset "Unification" begin
        include("unification_test.jl")
    end

    @testset "Facts" begin
        include("fact_test.jl")
    end

    @testset "Context Rewriting" begin
        include("context_rewriting_tests.jl")
    end

    @testset "Predicate Substitution" begin
        include("predicate_substitution_test.jl")
    end

    @testset "Locators" begin
        include("locator_test.jl")
    end

    @testset "Strategy & Search" begin
        include("strategy_test.jl")
    end

    @testset "Simplification" begin
        include("simplification_test.jl")
    end

    @testset "Ring Normalization" begin
        include("ring_test.jl")
    end

    @testset "Dynamic Tactics" begin
        include("dynamic_tactic_test.jl")
    end
end
include("dynamic_tactic_test.jl")
