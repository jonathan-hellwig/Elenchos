"""
    Strategy — non-deterministic tactic programs for Elenchos.

A `Strategy` is an AST describing a (possibly non-deterministic) program
of atomic tactics.  A **solver** explores the strategy and returns a
`Trace` (`Vector{Tactic}`) — the concrete sequence of atomic steps.

Replaying a trace on a proof state is cheap and deterministic.  Finding
the trace is the hard part (search).

# AST nodes

    Choice(a, b, c, ...)   Non-deterministic choice (solver picks).
    Then(a, b, c, ...)     Sequential composition.
    Repeat(body)           Iterate body until failure (zero or more).
    Skip()                 Do nothing.

Subgoal scheduling: tactics with `subgoal_idx = nothing` auto-search.
DFS explores `Choice` branches left-to-right; BFS forks them.

# Architecture

    Strategy    AST node (data, not callable)
    Tactic      Leaf: an atomic tactic struct
    Solver      solve_dfs(strategy, proof) -> (Derivation, Trace)
    Trace       Vector{Tactic} — deterministic replay recipe

# Usage

    strategy = Choice(id(), Then(implies_right(), id()))
    (proof′, trace) = solve_dfs(strategy, proof)

    # Replay a trace cheaply:
    proof′′ = replay(trace, proof)   # proof′′ == proof′
"""
module Strategy

using ..Kernel
using ..Tactics: Tactic, TacticFailure
import ..Syntax: _INode, _fill_nth_open, _render_inference, _plain_sequent

export AbstractStrategy
export Then, Choice, Repeat, Skip
export solve_dfs, solve_bfs, solve_greedy, replay, Trace, print_tactic_proof
export MaxStepsExceeded

# ══════════════════════════════════════════════════════════════════════════════
#                           STRATEGY AST
# ══════════════════════════════════════════════════════════════════════════════

abstract type AbstractStrategy end

"""Node in a strategy tree: either an `AbstractStrategy` or an atomic `Tactic`."""
const StrategyNode = Union{AbstractStrategy,Tactic}

"""Non-deterministic choice over `branches`.  The solver decides the order."""
struct Choice <: AbstractStrategy
    branches::Vector{StrategyNode}
end

"""Sequential composition: run `steps` in order."""
struct Then <: AbstractStrategy
    steps::Vector{StrategyNode}
end

"""Repeat body zero or more times until failure."""
struct Repeat <: AbstractStrategy
    body::StrategyNode
end

"""Do nothing (identity strategy)."""
struct Skip <: AbstractStrategy end

# Vararg constructors — the natural way to build these.
Choice(args::StrategyNode...) = Choice(StrategyNode[args...])
Then(args::StrategyNode...) = Then(StrategyNode[args...])

# ══════════════════════════════════════════════════════════════════════════════
#                          TRACE TYPE
# ══════════════════════════════════════════════════════════════════════════════

const Trace = Vector{Tactic}

"""
    replay(trace, proof) -> Derivation

Deterministically replay a trace of atomic tactics on a proof state.
"""
function replay(trace::Trace, proof::Derivation)
    for t in trace
        proof = t(proof)
    end
    proof
end

# ══════════════════════════════════════════════════════════════════════════════
#                         DFS SOLVER
# ══════════════════════════════════════════════════════════════════════════════
struct MaxStepsExceeded <: Exception end
"""
    solve_dfs(strategy, proof; max_steps=10000) -> (Derivation, Trace)

Depth-first solver with full backtracking: explore the strategy and return
the first successful path. Unlike greedy solvers, this will backtrack
across `Then` and `Repeat` boundaries if a subsequent step fails.

Throws `TacticFailure` if no path closes the proof or strategy terminates
without a solution.
"""
function solve_dfs(strategy::StrategyNode, proof::Derivation; max_steps::Int=10000)
    # WorkItem: (current_proof, current_trace, remaining_work)
    WorkItem = Tuple{Derivation,Trace,Vector{StrategyNode}}

    stack = WorkItem[(proof, Tactic[], StrategyNode[strategy])]
    steps_left = Ref(max_steps)

    while !isempty(stack)
        p, tr, remaining = pop!(stack)

        # Early exit: if the proof is already closed, we are done!
        if isempty(p.assumptions)
            return (p, tr)
        end

        # Strategy exhausted on this branch WITHOUT closing the proof: 
        # This is a failure in search mode — backtrack!
        if isempty(remaining)
            continue
        end

        # Process the next node in this branch
        head = remaining[1]
        rest = remaining[2:end]

        _dfs_expand!(stack, p, tr, head, rest, steps_left)
    end

    throw(TacticFailure("solve_dfs: No branch succeeded"))
end

# ── DFS Expansion ────────────────────────────────────────────────────────────

# Atomic tactics cost 1 step.
function _dfs_expand!(stack, p::Derivation, tr::Trace, node::Tactic,
    rest::Vector{StrategyNode}, steps::Ref{Int})

    # 1. Check for 'nothing' locators that need solver-controlled expansion
    expansion = _try_expand_tactic(node, p)
    if expansion !== nothing
        _dfs_expand!(stack, p, tr, expansion, rest, steps)
        return
    end

    # 2. Standard execution
    steps[] <= 0 && throw(MaxStepsExceeded())
    steps[] -= 1
    try
        p′ = node(p)
        push!(stack, (p′, Tactic[tr...; node], rest))
    catch e
        e isa TacticFailure || rethrow()
    end
end

# ── Tactic Expansion Helpers ──────────────────────────────────────────────────

function _try_expand_tactic(node::T, p::Derivation) where T<:Tactic
    # We only expand if the tactic has an open subgoal_idx or is targeting subgoal 1.
    sidx = node.subgoal_idx === nothing ? 1 : node.subgoal_idx
    (sidx < 1 || sidx > length(p.assumptions)) && return nothing
    seq = p.assumptions[sidx]

    for f in fieldnames(T)
        f === :subgoal_idx && continue
        val = getfield(node, f)
        if val === nothing
            ft = fieldtype(T, f)
            branches = nothing
            if _is_cons_locator(ft)
                branches = [
                    _with_field(node, f, Cons(i))
                    for i in 1:length(seq.consequent)
                ]
            elseif _is_ante_locator(ft)
                branches = [
                    _with_field(node, f, Ante(i))
                    for i in 1:length(seq.antecedent)
                ]
            end

            if branches !== nothing
                # Fix the subgoal_idx so branches are stable
                stable_branches = [_with_field(b, :subgoal_idx, sidx) for b in branches]
                return Choice(stable_branches...)
            end
        end
    end
    return nothing
end

# Create a new tactic instance with one field updated
function _with_field(node::T, field::Symbol, value) where T<:Tactic
    args = Any[(f == field ? value : getfield(node, f)) for f in fieldnames(T)]
    return T(args...)
end

_is_cons_locator(T::Type) = T <: Cons || (T isa Union && (_is_cons_locator(T.a) || _is_cons_locator(T.b)))
_is_ante_locator(T::Type) = T <: Ante || (T isa Union && (_is_ante_locator(T.a) || _is_ante_locator(T.b)))


# Skip is free (bookkeeping).
function _dfs_expand!(stack, p::Derivation, tr::Trace, ::Skip,
    rest::Vector{StrategyNode}, ::Ref{Int})
    push!(stack, (p, tr, rest))
end

# Then is free (bookkeeping).
function _dfs_expand!(stack, p::Derivation, tr::Trace, node::Then,
    rest::Vector{StrategyNode}, ::Ref{Int})
    push!(stack, (p, tr, StrategyNode[node.steps; rest]))
end

# Choice costs 1 step (explores a new branch).
function _dfs_expand!(stack, p::Derivation, tr::Trace, node::Choice,
    rest::Vector{StrategyNode}, steps::Ref{Int})
    steps[] <= 0 && throw(MaxStepsExceeded())
    steps[] -= 1
    for i in length(node.branches):-1:1
        push!(stack, (p, tr, StrategyNode[node.branches[i]; rest]))
    end
end

# Repeat costs 1 step (deciding whether to continue the loop).
function _dfs_expand!(stack, p::Derivation, tr::Trace, node::Repeat,
    rest::Vector{StrategyNode}, steps::Ref{Int})
    steps[] <= 0 && throw(MaxStepsExceeded())
    steps[] -= 1
    # Priority: zero iterations (Skip), then one+ iterations (Longest first)
    push!(stack, (p, tr, rest))
    push!(stack, (p, tr, StrategyNode[node.body, node, rest...]))
end

# ══════════════════════════════════════════════════════════════════════════════
#                         BFS SOLVER
# ══════════════════════════════════════════════════════════════════════════════

"""
    solve_bfs(strategy, proof; max_depth=100) -> (Derivation, Trace)

Breadth-first solver: explore the strategy level by level, returning the
*shortest* trace that closes the proof.

Unlike `solve_dfs`, which commits to the first succeeding `Choice` branch,
BFS explores all branches at each depth and finds the shallowest solution.

Throws `TacticFailure` if no closed proof is found within `max_depth` levels.
"""
function solve_bfs(strategy::StrategyNode, proof::Derivation; max_depth::Int=100)
    # Each work item: (proof_state, trace_so_far, remaining_strategy_steps)
    WorkItem = Tuple{Derivation,Trace,Vector{StrategyNode}}

    # Check if already closed
    isempty(proof.assumptions) && return (proof, Tactic[])

    queue = WorkItem[(proof, Tactic[], StrategyNode[strategy])]

    for _depth in 1:max_depth
        isempty(queue) && throw(TacticFailure("BFS: search space exhausted"))
        next_queue = WorkItem[]
        for (p, tr, remaining) in queue
            if isempty(remaining)
                # Strategy exhausted without closing — dead end
                continue
            end
            head = remaining[1]
            rest = remaining[2:end]
            _bfs_expand!(next_queue, p, tr, head, rest)
        end
        # Check if any new state has a closed proof
        for (p, tr, remaining) in next_queue
            if isempty(p.assumptions)
                return (p, tr)
            end
        end
        queue = next_queue
    end
    throw(TacticFailure("BFS: max depth $max_depth exceeded"))
end

function _bfs_expand!(queue, p::Derivation, tr::Trace, node::Tactic,
    rest::Vector{StrategyNode})
    try
        p′ = node(p)
        push!(queue, (p′, Tactic[tr; node], rest))
    catch e
        e isa TacticFailure || rethrow()
        # Dead end — don't enqueue
    end
end

function _bfs_expand!(queue, p::Derivation, tr::Trace, node::Skip,
    rest::Vector{StrategyNode})
    push!(queue, (p, tr, rest))
end

function _bfs_expand!(queue, p::Derivation, tr::Trace, node::Then,
    rest::Vector{StrategyNode})
    # Prepend Then's steps to the remaining work
    new_rest = StrategyNode[node.steps; rest]
    push!(queue, (p, tr, new_rest))
end

function _bfs_expand!(queue, p::Derivation, tr::Trace, node::Choice,
    rest::Vector{StrategyNode})
    # Fork: one queue entry per branch
    for branch in node.branches
        push!(queue, (p, tr, StrategyNode[branch; rest]))
    end
end

function _bfs_expand!(queue, p::Derivation, tr::Trace, node::Repeat,
    rest::Vector{StrategyNode})
    # Repeat = Choice(Skip, Then(body, Repeat(body)))
    # Zero iterations: skip the repeat
    push!(queue, (p, tr, rest))
    # One+ iterations: do body, then repeat again
    push!(queue, (p, tr, StrategyNode[node.body, node, rest...]))
end

# ══════════════════════════════════════════════════════════════════════════════
#                        GREEDY SOLVER (no trace, no backtrack)
# ══════════════════════════════════════════════════════════════════════════════

"""
    solve_greedy(strategy, proof) -> Derivation

Greedy forward-only solver: applies the strategy to the proof state and
returns the resulting `Derivation`.  Unlike `solve_dfs`, it:

  - **Never collects a trace** — no `Vector{Tactic}` is allocated.
  - **Never backtracks across `Then` steps** — if step k in a sequence
    fails after steps 1…k-1 have already advanced the proof, the failure
    propagates immediately rather than rolling back to try another `Choice`
    branch that might have produced this same `Then`.

`Choice` still tries branches left-to-right and commits to the first success
at the *top of that Choice node*, so `Repeat(Choice(a, b, c, ...))` works
correctly: each iteration tries a, then b, then c until one fires.

This is the right solver for deterministic strategy pipelines like
`ring_norm()` where no genuine backtracking is required.
Use `solve_dfs` when you need a replay trace or true multi-level backtracking.
"""
function solve_greedy(s::StrategyNode, p::Derivation)
    _greedy(s, p)
end

# Leaf: atomic tactic — just apply it (throws TacticFailure on failure).
_greedy(t::Tactic, p::Derivation) = t(p)

# Skip: identity.
_greedy(::Skip, p::Derivation) = p

# Then: run each step in sequence, propagate any failure immediately.
function _greedy(s::Then, p::Derivation)
    for step in s.steps
        p = _greedy(step, p)
    end
    p
end

# Choice: try branches left-to-right, commit to the first that succeeds.
function _greedy(s::Choice, p::Derivation)
    for (i, branch) in enumerate(s.branches)
        try
            return _greedy(branch, p)
        catch e
            e isa TacticFailure || rethrow()
            i == length(s.branches) && rethrow()
        end
    end
    throw(TacticFailure("Choice: no branches"))
end

# Repeat: keep applying until the body throws TacticFailure.
function _greedy(s::Repeat, p::Derivation)
    while true
        try
            p = _greedy(s.body, p)
        catch e
            e isa TacticFailure || rethrow()
            break
        end
    end
    p
end

function (s::AbstractStrategy)(p::Derivation)
    # Default to greedy solver for interactive use (no trace, no backtrack).
    # Use solve_dfs explicitly when a replay trace or true backtracking is needed.
    solve_greedy(s, p)
end

# ══════════════════════════════════════════════════════════════════════════════
#                       TACTIC-LEVEL PROOF DISPLAY
# ══════════════════════════════════════════════════════════════════════════════

"""
    _tactic_label(t::Tactic) -> String

Human-readable label for a tactic, including its arguments.
Skips `subgoal_idx` and `nothing`-valued optional fields.
"""
function _tactic_label(t::Tactic)::String
    T = typeof(t)
    name = T.name.name  # struct name, e.g. :ImpliesRight
    fnames = fieldnames(T)
    parts = String[]
    for fn in fnames
        fn === :subgoal_idx && continue
        fn === :target_idx && continue
        val = getfield(t, fn)
        val === nothing && continue
        # Show derivation fields by their conclusion, not the full proof tree.
        if val isa Derivation
            push!(parts, _plain_sequent(val.conclusion))
        else
            push!(parts, string(val))
        end
    end
    isempty(parts) ? string(name) : string(name, "(", join(parts, ", "), ")")
end

"""
    _find_targeted_subgoal(t::Tactic, p::Derivation) -> Int

Determine which subgoal a tactic targets. Uses `subgoal_idx` if set,
otherwise tries each subgoal (same logic as the auto-search dispatch).
"""
function _find_targeted_subgoal(t::Tactic, p::Derivation)::Int
    t.subgoal_idx !== nothing && return t.subgoal_idx
    for i in 1:length(p.assumptions)
        try
            t(p, i)
            return i
        catch e
            e isa TacticFailure || rethrow()
        end
    end
    error("Tactic didn't succeed on any subgoal during tree construction")
end

"""
    print_tactic_proof([io], trace, initial)

Print a tactic-level proof as an inference tree in Gentzen style.

`trace` is the `Vector{Tactic}` from `solve_dfs` (or built manually).
`initial` is the starting derivation (from `start_proof`).

Each tactic application becomes one inference node — premises above
the line are the subgoals it created, the conclusion below is the
sequent it operated on.  Derived tactics like `Rewrite` that expand
to many kernel steps appear as a single node.
"""
print_tactic_proof(trace::Vector{<:Tactic}, initial::Derivation) =
    print_tactic_proof(stdout, trace, initial)

function print_tactic_proof(io::IO, trace::Vector{<:Tactic}, initial::Derivation)
    # Start with one open leaf for the goal
    tree = _INode("?", _plain_sequent(initial.conclusion), _INode[], true)

    p = initial
    for t in trace
        idx = _find_targeted_subgoal(t, p)
        target = p.assumptions[idx]

        # Apply tactic
        p_next = t(p, idx)

        # New subgoals: the tactic replaced 1 subgoal at idx with n_new
        n_before = length(p.assumptions)
        n_after = length(p_next.assumptions)
        n_new = n_after - n_before + 1

        new_goals = if n_new > 0
            Tuple(p_next.assumptions[i] for i in idx:(idx+n_new-1))
        else
            ()
        end

        # Build inference node
        prems = [_INode("?", _plain_sequent(s), _INode[], true) for s in new_goals]
        node = _INode(_tactic_label(t), _plain_sequent(target), prems, false)

        # Fill the idx-th open slot in the tree
        tree = _fill_nth_open(tree, idx, node)
        p = p_next
    end

    # Render with the same Gentzen-style renderer
    rendered = _render_inference(tree)
    for line in rendered.lines
        println(io, line)
    end
end

# ══════════════════════════════════════════════════════════════════════════════
#                              SHOW
# ══════════════════════════════════════════════════════════════════════════════

Base.show(io::IO, ::Skip) = print(io, "skip")
Base.show(io::IO, s::Repeat) = print(io, "repeat(", s.body, ")")

function Base.show(io::IO, s::Choice)
    print(io, "choice(")
    join(io, s.branches, ", ")
    print(io, ")")
end

function Base.show(io::IO, s::Then)
    print(io, "then(")
    join(io, s.steps, ", ")
    print(io, ")")
end

end # module Strategy
