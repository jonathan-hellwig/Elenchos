using Test
using Elenchos
using Elenchos.Strategy
using Elenchos.BaseTactics
using Elenchos.DerivedTactics
using Elenchos.Tactics
using Elenchos.Strategies
using Elenchos.Syntax

@testset "Dynamic Tactic Target Discovery" begin
    let x = Variable("x")
        
        @testset "Simple target discovery in multiple consequents" begin
            # x ≤ 2 ⊢ x ≤ 0, x ≤ 3, x ≤ -1
            seq = (x ≤ 2,) ⊢ (x ≤ 0, x ≤ 3, x ≤ -1)
            p = start_proof(seq)
            strat = lin_arith(target_idx=nothing)
            p_solved, trace = solve_dfs(strat, p)
            @test isempty(p_solved.assumptions)
        end

        @testset "Repeated discovery with multiple subgoals" begin
            # Using And (∧) right expansion to create multiple subgoals.
            # (x ≤ 4) ∧ (x ≤ 3) results in two subgoals:
            # 1: x ≤ 2 ⊢ x ≤ 4, x ≤ 0
            # 2: x ≤ 2 ⊢ x ≤ 3, x ≤ 0
            # By not using prop() we avoid it unpacking the `Not()` inside `≤`.
            seq = (x ≤ 2,) ⊢ ((x ≤ 4) ∧ (x ≤ 3), x ≤ 0)
            p = start_proof(seq)
            strat = Repeat(Choice(lin_arith(target_idx=nothing), and_right(target_idx=nothing)))
            p_solved, trace = solve_dfs(strat, p)
            @test isempty(p_solved.assumptions)
        end

        @testset "OR logical expansion requiring prop branching" begin
            # This directly captures the originally problematic user example.
            # The solver needs to:
            # 1. Backtrack successfully when implies_right fails (due to strict inequality).
            # 2. Select or_right to generate multiple consequents.
            # 3. Synthesize the lin_arith expansion with Cons indices until one clears.
            seq = (x ≤ 2,) ⊢ ((x ≤ 3) ∨ (x ≤ 0))
            p = start_proof(seq)
            strat = Repeat(Choice(lin_arith(target_idx=nothing), prop()))
            p_solved, trace = solve_dfs(strat, p)
            @test isempty(p_solved.assumptions)
        end
        
        @testset "Complex nested expansion" begin
            seq = (x ≤ 2,) ⊢ (((x ≤ 3) ∧ (x ≤ 4)) ∧ (x ≤ 5), x ≤ 0)
            p = start_proof(seq)
            strat = Repeat(Choice(lin_arith(target_idx=nothing), and_right(target_idx=nothing)))
            p_solved, trace = solve_dfs(strat, p)
            @test isempty(p_solved.assumptions)
        end
    end
end
