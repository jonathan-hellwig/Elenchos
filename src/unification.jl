# ═══════════════════════════════════════════════════════════════════════════════
#                         UNIFICATION MODULE
# ═══════════════════════════════════════════════════════════════════════════════
#
# Infrastructure for pattern matching used by tactics.
# This module provides:
#   - is_ground: Check if a term/formula contains no variables
#   - match_subterm: Find where a pattern matches inside a term
#   - unify: Unify schematic patterns against concrete terms (returns Substitution or nothing)
# ═══════════════════════════════════════════════════════════════════════════════

module Unification

using ..Kernel

export is_ground, match_subterm, unify_subterm, unify_subterm_formula
export unify, is_schematic, search_sequent
export find_first_in_sequent

# ─────────────────────────────────────────────────────────────────────────────
#                              is_ground
# ─────────────────────────────────────────────────────────────────────────────

"""
    is_ground(expr) -> Bool

Check if an expression contains no variables.
Ground terms/formulas can be evaluated to constants.
Quantified formulas are considered non-ground.
"""
is_ground(::Variable) = false
is_ground(::Forall) = false   # Quantified formulas are not ground
is_ground(expr) = all(is_ground, children(expr))  # recurse via Walkers

# ─────────────────────────────────────────────────────────────────────────────
#                    EXPRESSION WALKERS (from Walkers module)
# ─────────────────────────────────────────────────────────────────────────────

# Re-export walker functions for backwards compatibility
using ..Walkers: children, reconstruct, transform, fold
using ..Walkers: find_subterm, find_subterm_formula
using ..Walkers: formula_kind, operands, logical_reconstruct, primitive_kind
using ..Walkers: all_matches_formula, all_matches_term
export children, reconstruct, transform, fold
export find_subterm, find_subterm_formula, unify
export formula_kind, operands, logical_reconstruct, primitive_kind

# ─────────────────────────────────────────────────────────────────────────────
#                    UNIFICATION
#         Match axiom schemas against concrete formulas
# ─────────────────────────────────────────────────────────────────────────────

"""
    is_schematic(term::Term) -> Union{FunctionSymbol, Nothing}

Check if term is a nullary function application (an uninterpreted constant).
During unification these act as pattern variables — they can be bound to any
term.  There is nothing inherently "schematic" about them; every
`FunctionSymbol` is uninterpreted, so any nullary application is bindable.
"""
function is_schematic(term::Term)
    term isa FunctionApplication || return nothing
    isempty(term.arguments) || return nothing
    return term.symbol
end

# Internal mutable state for unification
const _UNIFY_WORKSPACE = Dict{FunctionSymbol,Term}()

"""
    unify(pattern::Term, target::Term) -> Union{Substitution, Nothing}

Unify a schematic pattern against a concrete target term.
Returns a Substitution with bindings for schematic symbols, or `nothing` on failure.
"""
function unify(pattern::Term, target::Term)
    empty!(_UNIFY_WORKSPACE)
    if _unify!(_UNIFY_WORKSPACE, pattern, target)
        Substitution(copy(_UNIFY_WORKSPACE))
    else
        nothing
    end
end

function unify(pattern::Formula, target::Formula)
    empty!(_UNIFY_WORKSPACE)
    if _unify!(_UNIFY_WORKSPACE, pattern, target)
        Substitution(copy(_UNIFY_WORKSPACE))
    else
        nothing
    end
end

# --- Internal unification helpers ---

function _unify!(state::Dict{FunctionSymbol,Term}, pattern::Term, target::Term)
    # Check if pattern is a schematic variable
    sym = is_schematic(pattern)
    if sym !== nothing
        # Schematic variable: bind or check consistency
        if haskey(state, sym)
            return state[sym] == target
        else
            state[sym] = target
            return true
        end
    end

    # Same type, recurse into structure
    typeof(pattern) == typeof(target) || return false

    # Manual unrolling of _unify_same_type! to avoid dynamic dispatch
    if pattern isa Sum
        return _unify!(state, pattern.left, (target::Sum).left) && _unify!(state, pattern.right, (target::Sum).right)
    elseif pattern isa Product
        return _unify!(state, pattern.left, (target::Product).left) && _unify!(state, pattern.right, (target::Product).right)
    elseif pattern isa Variable
        return pattern == target
    elseif pattern isa Constant
        return pattern == target
    elseif pattern isa Difference
        return _unify!(state, pattern.left, (target::Difference).left) && _unify!(state, pattern.right, (target::Difference).right)
    elseif pattern isa Division
        return _unify!(state, pattern.left, (target::Division).left) && _unify!(state, pattern.right, (target::Division).right)
    elseif pattern isa Power
        return _unify!(state, pattern.base, (target::Power).base) && _unify!(state, pattern.exponent, (target::Power).exponent)
    elseif pattern isa FunctionApplication
        target_fa = target::FunctionApplication
        pattern.symbol == target_fa.symbol || return false
        length(pattern.arguments) == length(target_fa.arguments) || return false
        for (pa, ta) in zip(pattern.arguments, target_fa.arguments)
            _unify!(state, pa, ta) || return false
        end
        return true
    elseif pattern isa Hole
        return pattern == target
    end
    return false
end

# Formula unification
function _unify!(state::Dict{FunctionSymbol,Term}, p::Formula, t::Formula)
    typeof(p) == typeof(t) || return false

    if p isa LessThan
        return _unify!(state, p.left, (t::LessThan).left) && _unify!(state, p.right, (t::LessThan).right)
    elseif p isa Equals
        return _unify!(state, p.left, (t::Equals).left) && _unify!(state, p.right, (t::Equals).right)
    elseif p isa Not
        return _unify!(state, p.formula, (t::Not).formula)
    elseif p isa Implies
        return _unify!(state, p.left, (t::Implies).left) && _unify!(state, p.right, (t::Implies).right)
    elseif p isa Forall
        p.variable == (t::Forall).variable || return false
        return _unify!(state, p.body, (t::Forall).body)
    elseif p isa PredicateApplication
        target_pa = t::PredicateApplication
        p.symbol == target_pa.symbol || return false
        length(p.arguments) == length(target_pa.arguments) || return false
        for (pa, ta) in zip(p.arguments, target_pa.arguments)
            _unify!(state, pa, ta) || return false
        end
        return true
    end
    return false
end

# ─────────────────────────────────────────────────────────────────────────────
#                            match_subterm
# ─────────────────────────────────────────────────────────────────────────────

"""
    match_subterm(pattern::Term, term::Term) -> Union{Term, Nothing}

Find the first subterm of `term` that matches `pattern`.
Returns the context with a `Hole(1)` at the match position, or `nothing` if no match found.

Uses structural equality for matching.
"""
function match_subterm(pattern::Term, term::Term)
    result = find_subterm(t -> t == pattern ? true : nothing, term)
    result === nothing ? nothing : result[2]
end

"""
    unify_subterm(pattern::Term, term::Term) -> Union{Tuple{Substitution, Term}, Nothing}

Find the first subterm of `term` that *unifies* with the schematic `pattern`.
Returns `(σ, context)` where `σ` is the substitution and `context` has `Hole(1)`
at the match site, or `nothing` if no subterm unifies.

Unlike `match_subterm` (which uses structural equality), this uses schematic
unification — so `pattern` may contain schematic variables like `_x`, `_y`.
"""
unify_subterm(pattern::Term, term::Term) = find_subterm(t -> unify(pattern, t), term)

# ─────────────────────────────────────────────────────────────────────────────
#                       unify_subterm_formula
# ─────────────────────────────────────────────────────────────────────────────

"""
    unify_subterm_formula(pattern::Term, formula::Formula)
        -> Union{Tuple{Substitution, Formula}, Nothing}

Find the first subterm inside `formula` that unifies with the schematic `pattern`.
Returns `(σ, formula_context)` where the context has `Hole(1)` at the matched
position, or `nothing` if no match is found.

Walks the formula at the *logical* level via `formula_kind`/`operands`, so
defined connectives (Equals, And, Or, …) are handled correctly — a single
rewrite step affects all syntactic positions belonging to one logical operand.
"""
unify_subterm_formula(pattern::Term, formula::Formula) =
    find_subterm_formula(t -> unify(pattern, t), formula)

function match_subterm_formula(pattern::Term, formula::Formula)
    result = find_subterm_formula(t -> t == pattern ? true : nothing, formula)
    result === nothing ? nothing : result[2]
end

# ─────────────────────────────────────────────────────────────────────────────
#                         SEQUENT SEARCH
# ─────────────────────────────────────────────────────────────────────────────

"""
    MatchSite{T}

A structure representing a match found within a sequent.
"""
struct MatchSite{T}
    pos::SequentPosition
    formula::Formula
    data::T
end

# Clean printing for individual sites
function Base.show(io::IO, m::MatchSite)
    print(io, "MatchSite(", m.pos, " → ", m.formula, ")")
end

"""
    SequentMatches

A wrapper for an iterator of `MatchSite` objects.
"""
struct SequentMatches
    ites
    pattern::Term
end

Base.iterate(sm::SequentMatches, args...) = Base.iterate(sm.ites, args...)
Base.IteratorSize(::Type{SequentMatches}) = Base.SizeUnknown()
Base.eltype(::Type{SequentMatches}) = MatchSite

function Base.show(io::IO, sm::SequentMatches)
    print(io, "SequentMatches(", sm.pattern, ")")
end

function Base.show(io::IO, ::MIME"text/plain", sm::SequentMatches)
    println(io, "SequentMatches iterator")
    println(io, "  Pattern: ", sm.pattern)
    print(io, "  Status:  Lazy (iterate or collect to view contents)")
end

"""
    search_sequent(f::Function, seq::Sequent; pos=nothing)

Apply a search function `f` to formulas in a sequent and return an iterator of `MatchSite`s.
"""
function search_sequent(f::Function, seq::Sequent; pos::Union{SequentPosition,Nothing}=nothing)
    if pos !== nothing
        fml = if pos isa Ante
            seq.antecedent[pos.idx]
        else
            seq.consequent[pos.idx]
        end
        return (MatchSite(pos, fml, res) for res in f(fml))
    end
    ante_ites = (MatchSite(Ante(idx), fml, res) for (idx, fml) in enumerate(seq.antecedent) for res in f(fml))
    cons_ites = (MatchSite(Cons(idx), fml, res) for (idx, fml) in enumerate(seq.consequent) for res in f(fml))
    return Iterators.flatten((ante_ites, cons_ites))
end

"""
    unify_sequent(seq::Sequent, pattern::Term; pos=nothing) -> SequentMatches

Find all occurrences of a pattern within a sequent and return a lazy iterator of matches.
"""
function unify_sequent(seq::Sequent, pattern::Term; pos::Union{SequentPosition,Nothing}=nothing)
    ites = search_sequent(seq; pos=pos) do fml
        all_matches_formula(t -> unify(pattern, t), fml)
    end
    return SequentMatches(ites, pattern)
end

"""
    find_first_in_sequent(pred, seq::Sequent; pos=nothing) -> Union{MatchSite, Nothing}

Find the first term-level subterm in `seq` where `pred(t)` returns non-`nothing`,
using early-exit tree traversal via `find_subterm_formula`.

The predicate `pred` should return the value to store in `MatchSite.data[1]` on a
match, or `nothing` to skip.  The returned `MatchSite` has
`data = (pred_result, formula_context)` where `formula_context` has `Hole(1)` at
the matched term position — the same shape as results from `unify_sequent`.

`pos` restricts the search to one formula; otherwise antecedent is searched first,
then consequent.

Much faster than `unify_sequent + iterate` when only one match is needed: the
tree walk stops immediately after the first hit and no Vector is ever allocated.
"""
function find_first_in_sequent(pred, seq::Sequent;
    pos::Union{SequentPosition,Nothing}=nothing)
    if pos !== nothing
        fml = pos isa Ante ? seq.antecedent[pos.idx] : seq.consequent[pos.idx]
        result = find_subterm_formula(pred, fml)
        result === nothing && return nothing
        return MatchSite(pos, fml, result)
    end
    for (idx, fml) in enumerate(seq.antecedent)
        result = find_subterm_formula(pred, fml)
        result !== nothing && return MatchSite(Ante(idx), fml, result)
    end
    for (idx, fml) in enumerate(seq.consequent)
        result = find_subterm_formula(pred, fml)
        result !== nothing && return MatchSite(Cons(idx), fml, result)
    end
    return nothing
end

end # module Unification
