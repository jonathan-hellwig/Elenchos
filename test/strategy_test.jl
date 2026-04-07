using Test
using Elenchos.Kernel
using Elenchos.Syntax
using Elenchos.Tactics: Tactic, TacticFailure
using Elenchos.BaseTactics
using Elenchos.Strategy: AbstractStrategy, Choice, Then, Repeat, Skip,
    solve_dfs, solve_bfs, solve_greedy, replay, Trace, MaxStepsExceeded
using Elenchos.Strategies: prop

@vars x y
@preds P Q R

A = P(x)
B = Q(y)
C = R(x)

@testset "Strategy & Search" begin

    # ═══════════════════════════════════════════════════════════════════════════════
    #                         AST CONSTRUCTION
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "AST nodes" begin
        @testset "Choice is n-ary" begin
            c1 = Choice(id())
            @test c1 isa Choice
            @test length(c1.branches) == 1

            c2 = Choice(id(), not_right())
            @test length(c2.branches) == 2

            c5 = Choice(id(), not_right(), not_left(), and_left(), or_right())
            @test length(c5.branches) == 5
        end

        @testset "Then is n-ary" begin
            t1 = Then(id())
            @test t1 isa Then
            @test length(t1.steps) == 1

            t3 = Then(implies_right(), not_right(), id())
            @test length(t3.steps) == 3
        end

        @testset "Repeat wraps a single body" begin
            r = Repeat(id())
            @test r isa Repeat
            @test r.body isa Id
        end

        @testset "Skip is a singleton" begin
            @test Skip() isa Skip
            @test Skip() isa AbstractStrategy
        end

        @testset "nested ASTs" begin
            s = Choice(Then(implies_right(), id()), Repeat(not_left()), Skip())
            @test s isa Choice
            @test length(s.branches) == 3
            @test s.branches[1] isa Then
            @test s.branches[2] isa Repeat
            @test s.branches[3] isa Skip
        end

        @testset "Tactics are valid strategy nodes" begin
            c = Choice(id(), implies_right())
            @test c.branches[1] isa Tactic
            @test c.branches[2] isa Tactic
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                         SHOW
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "show" begin
        @test sprint(show, Skip()) == "skip"
        @test sprint(show, Repeat(id())) == "repeat(id)"
        @test sprint(show, Choice(id(), not_right())) == "choice(id, not_right)"
        @test sprint(show, Then(implies_right(), id())) == "then(implies_right, id)"
        # n-ary
        @test sprint(show, Choice(id(), not_right(), and_left())) ==
              "choice(id, not_right, and_left)"
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                         SOLVE_GREEDY
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "solve_greedy" begin
        @testset "atomic tactic" begin
            p = start_proof(Sequent((A,), (A,)))
            p2 = solve_greedy(id(), p)
            @test isempty(p2.assumptions)
        end

        @testset "Skip produces empty trace" begin
            p = start_proof(Sequent((A,), (A,)))
            p2 = solve_greedy(Skip(), p)
            @test p2.assumptions == p.assumptions  # unchanged
        end

        @testset "Then: sequential composition" begin
            p = start_proof(Sequent((), (A → A,)))
            p2 = solve_greedy(Then(implies_right(), id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Then: 3-step sequence" begin
            p = start_proof(Sequent((), (A → (B → A),)))
            p2 = solve_greedy(Then(implies_right(), implies_right(), id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Then: failure in middle aborts" begin
            p = start_proof(Sequent((A,), (A,)))
            # implies_right will fail — A is not an implication
            @test_throws TacticFailure solve_greedy(Then(implies_right(), id()), p)
        end

        @testset "Choice: first branch succeeds" begin
            p = start_proof(Sequent((A,), (A,)))
            p2 = solve_greedy(Choice(id(), implies_right()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Choice: fallback to later branch" begin
            p = start_proof(Sequent((A,), (A,)))
            p2 = solve_greedy(Choice(implies_right(), id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Choice: n-ary fallback to third branch" begin
            p = start_proof(Sequent((A,), (A,)))
            p2 = solve_greedy(Choice(implies_right(), not_right(), id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Choice: all branches fail → TacticFailure" begin
            p = start_proof(Sequent((A,), (B,)))
            @test_throws TacticFailure solve_greedy(Choice(id(), implies_right()), p)
        end

        @testset "Repeat: zero iterations (body fails immediately)" begin
            p = start_proof(Sequent((A,), (A,)))
            # implies_right fails on non-implication
            p2 = solve_greedy(Repeat(implies_right()), p)
            @test p2.assumptions == p.assumptions
        end

        @testset "Repeat: multiple iterations" begin
            p = start_proof(Sequent((), (A → (A → A),)))
            p2 = solve_greedy(Repeat(implies_right()), p)
            @test length(p2.assumptions) == 1
            @test p2.assumptions[1] == Sequent((A, A), (A,))
        end

        @testset "Repeat + Choice" begin
            p = start_proof(Sequent((), (A → A,)))
            p2 = solve_greedy(Repeat(Choice(implies_right(), id())), p)
            @test isempty(p2.assumptions)
        end

        @testset "nested Then in Choice" begin
            p = start_proof(Sequent((), (A → A,)))
            s = Choice(
                id(),                                    # fails (no identity on goal)
                Then(implies_right(), id()),             # succeeds
            )
            p2 = solve_greedy(s, p)
            @test isempty(p2.assumptions)
        end

        @testset "max_steps limit" begin
            p = start_proof(Sequent((), (A → (B → A),)))
            # Requires 2 implies_right steps to reach A, B ⊢ A, then 1 id step to close. Total 3.
            # If we limit to 2, it should fail.
            @test_throws MaxStepsExceeded solve_dfs(Repeat(Choice(implies_right(), id())), p; max_steps=2)

            # If we limit to 3, it should succeed.
            (p2, trace) = solve_dfs(Repeat(Choice(implies_right(), id())), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 3
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                   REPEAT FOR SATURATION
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "Repeat for saturation (formerly solve_saturate)" begin
        @testset "single subgoal, single step" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_dfs(Repeat(id()), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 1
        end

        @testset "multiple subgoals (auto-search)" begin
            p = start_proof(Sequent((A, B), (A ∧ B,)))
            p = and_right()(p)  # splits into two subgoals
            @test length(p.assumptions) == 2

            (p2, trace) = solve_dfs(Repeat(Id()), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 2
            @test all(t -> t isa Id, trace)
        end

        @testset "fixed subgoal_idx" begin
            p = start_proof(Sequent((A, B), (A ∧ B,)))
            p = and_right()(p)
            @test length(p.assumptions) == 2

            # Only close subgoal 2, leaving 1 open, which now throws
            @test_throws TacticFailure solve_dfs(Repeat(id(; subgoal_idx=2)), p)
        end

        @testset "saturates until fixpoint" begin
            # A → (B → A) requires two implies_right steps
            p = start_proof(Sequent((), (A → (B → A),)))
            # Close it fully to avoid crashing
            (p3, trace2) = solve_dfs(Then(Repeat(implies_right()), id()), p)
            @test isempty(p3.assumptions)
        end

        @testset "no progress → throws TacticFailure" begin
            p = start_proof(Sequent((A,), (B,)))
            @test_throws TacticFailure solve_dfs(Repeat(id()), p)
        end

        @testset "Choice + Repeat" begin
            p = start_proof(Sequent((), (A → A,)))
            (p2, trace) = solve_dfs(Repeat(Choice(implies_right(), id())), p)
            @test isempty(p2.assumptions)
            # Two steps: implies_right then id
            @test length(trace) == 2
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                         REPLAY
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "replay" begin
        @testset "replay reproduces solve_dfs result" begin
            seq = Sequent((), (A → A,))
            p = start_proof(seq)
            (p2, trace) = solve_dfs(Then(implies_right(), id()), p)
            @test isempty(p2.assumptions)

            p3 = replay(trace, start_proof(seq))
            @test isempty(p3.assumptions)
            @test p3.conclusion == p2.conclusion
        end

        @testset "replay reproduces prop() result" begin
            seq = Sequent((), ((A ∧ B) → (B ∧ A),))
            p = start_proof(seq)
            (p2, trace) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)

            p3 = replay(trace, start_proof(seq))
            @test isempty(p3.assumptions)
        end

        @testset "empty trace is no-op" begin
            seq = Sequent((A,), (A,))
            p = start_proof(seq)
            p2 = replay(Tactic[], p)
            @test p2.assumptions == p.assumptions
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                    PROP STRATEGY
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "prop()" begin
        @testset "returns a Repeat" begin
            @test prop() isa Choice
        end

        @testset "A → A" begin
            p = start_proof(Sequent((), (A → A,)))
            (p2, trace) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
            @test trace[1] isa ImpliesRight
            @test trace[2] isa Id
        end

        @testset "A ∧ B → B ∧ A" begin
            p = start_proof(Sequent((), ((A ∧ B) → (B ∧ A),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "A ∨ B → B ∨ A" begin
            p = start_proof(Sequent((), ((A ∨ B) → (B ∨ A),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "A, ¬A ⊢ B (ex falso)" begin
            p = start_proof(Sequent((A, ¬A), (B,)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "(A → B) → (¬B → ¬A) (contrapositive)" begin
            p = start_proof(Sequent((), ((A → B) → (¬B → ¬A),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "¬¬A → A (double negation elimination)" begin
            p = start_proof(Sequent((), (¬(¬A) → A,)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "A → ¬¬A (double negation introduction)" begin
            p = start_proof(Sequent((), (A → ¬(¬A),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "(A ∧ B) → A (conjunction elimination)" begin
            p = start_proof(Sequent((), ((A ∧ B) → A,)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "A → (A ∨ B) (disjunction introduction)" begin
            p = start_proof(Sequent((), (A → (A ∨ B),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "(A → C) → ((B → C) → ((A ∨ B) → C)) (or elimination)" begin
            p = start_proof(Sequent((), ((A → C) → ((B → C) → ((A ∨ B) → C)),)))
            (p2, _) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)
        end

        @testset "trace is a valid certificate" begin
            seq = Sequent((), ((A ∨ B) → (B ∨ A),))
            p = start_proof(seq)
            (p2, trace) = solve_dfs(Repeat(prop()), p)
            @test isempty(p2.assumptions)

            p3 = replay(trace, start_proof(seq))
            @test isempty(p3.assumptions)
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                    EDGE CASES & ERROR HANDLING
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "edge cases" begin
        @testset "single-branch Choice" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_dfs(Choice(id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "single-step Then" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_dfs(Then(id()), p)
            @test isempty(p2.assumptions)
        end

        @testset "Repeat terminates when body eventually fails" begin
            p = start_proof(Sequent((), (A → A,)))
            @test_throws TacticFailure solve_dfs(Repeat(implies_right()), p)
        end

        @testset "deeply nested strategy" begin
            # Choice(Then(Choice(id(), implies_right()), id()), Skip())
            p = start_proof(Sequent((), (A → A,)))
            s = Choice(
                Then(
                    Choice(id(), implies_right()),
                    id()
                ),
                Skip()
            )
            (p2, trace) = solve_dfs(s, p)
            # id() in inner Choice fails, implies_right succeeds, then id closes
            @test isempty(p2.assumptions)
            @test length(trace) == 2
        end

        @testset "TacticFailure propagates from all Choice branches" begin
            p = start_proof(Sequent((A,), (B,)))
            # Neither id nor implies_right can close A ⊢ B
            @test_throws TacticFailure solve_dfs(
                Choice(id(), implies_right(), not_right()), p)
        end
    end

    # ═══════════════════════════════════════════════════════════════════════════════
    #                         solve_bfs
    # ═══════════════════════════════════════════════════════════════════════════════

    @testset "solve_bfs" begin
        @testset "id closes trivial sequent" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_bfs(id(), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 1
            @test trace[1] isa Id
        end

        @testset "Then: sequential composition" begin
            p = start_proof(Sequent((), (A → A,)))
            (p2, trace) = solve_bfs(Then(implies_right(), id()), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 2
        end

        @testset "Choice: picks first working branch" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_bfs(Choice(not_right(), id()), p)
            @test isempty(p2.assumptions)
            @test trace[1] isa Id
        end

        @testset "Repeat: iterates until no more apply" begin
            p = start_proof(Sequent((), (A → (B → A),)))
            (p2, trace) = solve_bfs(Then(Repeat(implies_right()), id()), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 3  # implies_right, implies_right, id
        end

        @testset "Skip: passes through" begin
            p = start_proof(Sequent((A,), (A,)))
            (p2, trace) = solve_bfs(Then(Skip(), id()), p)
            @test isempty(p2.assumptions)
            @test length(trace) == 1
            @test trace[1] isa Id
        end

        @testset "failure when nothing works" begin
            p = start_proof(Sequent((A,), (B,)))
            @test_throws TacticFailure solve_bfs(
                Choice(id(), implies_right(), not_right()), p)
        end

        @testset "BFS finds short path through red herring" begin
            # Red herring: (A→B), C ⊢ C — id closes in 1 step,
            # but implies_left also succeeds and branches.
            p = start_proof(Sequent((A → B, C), (C,)))
            strat = Repeat(Choice(implies_left(), id()))
            (p2, trace) = solve_bfs(strat, p)
            @test isempty(p2.assumptions)
            @test length(trace) == 1  # BFS finds id immediately
            @test trace[1] isa Id
        end

        @testset "BFS vs DFS: BFS avoids exponential blowup" begin
            # (A₁→B₁), (A₂→B₂), C ⊢ C
            atoms = [P(Variable("z$i")) for i in 1:5]
            Cv = atoms[end]
            imps = [Implies(atoms[2i-1], atoms[2i]) for i in 1:2]
            seq = Sequent(tuple(imps..., Cv), (Cv,))

            strat = Repeat(Choice(implies_left(), id()))

            p1 = start_proof(seq)
            (_, tr_dfs) = solve_dfs(strat, p1)

            p2 = start_proof(seq)
            (_, tr_bfs) = solve_bfs(strat, p2)

            # DFS: 2^(n+1)-1 = 7 steps; BFS: 1 step
            @test length(tr_dfs) == 7
            @test length(tr_bfs) == 1
        end

        @testset "BFS agrees with DFS on prop() for standard theorems" begin
            theorems = [
                Sequent((), (A → A,)),              # A → A
                Sequent((), ((A → B) → (¬B → ¬A),)),  # contrapositive
            ]
            strat = Repeat(prop())
            for seq in theorems
                p1 = start_proof(seq)
                (r1, _) = solve_dfs(strat, p1)
                p2 = start_proof(seq)
                (r2, _) = solve_bfs(strat, p2)
                @test isempty(r1.assumptions)
                @test isempty(r2.assumptions)
            end
        end
    end

end # testset "Strategy & Search"
