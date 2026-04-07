"""
    Tactics infrastructure for Elenchos.

Each tactic is a struct `<: Tactic`.  The `@tactic` macro generates the
struct and plumbing; the user implements `Tactics.execute(::T, p, subgoal_idx)`.

The `execute` signature omits `seq` because it is always recoverable as
`p.assumptions[subgoal_idx]`.

## Subgoal selection

Every tactic has a `subgoal_idx` field of type `Union{Int,Nothing}`.

  - **Interactive use** (`subgoal_idx = 1`):  the factory function defaults
    to subgoal 1, e.g. `not_right()` targets the first open subgoal.
  - **Strategy template** (`subgoal_idx = nothing`):  the struct constructor
    defaults to `nothing`, e.g. `NotRight()` leaves the index unset.
    When called on a proof, the tactic automatically searches all open
    subgoals (last-to-first) for one it can apply to.
"""
module Tactics

using ..Kernel
using ..Syntax

export Tactic, TacticFailure, @tactic, execute
export First, resolve_cons, resolve_ante

# ══════════════════════════════════════════════════════════════════════════════
#                           LOCATOR: First
# ══════════════════════════════════════════════════════════════════════════════

"""
    First()

A search-based locator: when resolved against a sequent with a predicate,
it finds the first formula that matches. Used as the default for interactive
tactic calls.

For solver-controlled search, set the locator to `nothing`. The solver
will expand the tactic into a `Choice` over all valid positions.
Calling a tactic with `nothing` directly will result in a `MethodError`.
"""
struct First end

"""
    resolve_cons(loc, seq, predicate) -> Cons

Resolve a consequent locator against a sequent using a predicate.
  - `First()`: search for the first matching formula in the consequent.
  - `Cons(i)`: validate that the formula at index `i` matches the predicate.
"""
function resolve_cons(::First, seq::Sequent, predicate::Function)
    idx = findfirst(predicate, seq.consequent)
    idx === nothing && throw(TacticFailure("No matching formula in consequent"))
    return Cons(idx)
end

function resolve_cons(loc::Cons, seq::Sequent, predicate::Function)
    1 <= loc.idx <= length(seq.consequent) ||
        throw(TacticFailure("Cons index $(loc.idx) out of bounds ($(length(seq.consequent)) in consequent)"))
    predicate(seq.consequent[loc.idx]) ||
        throw(TacticFailure("Formula at Cons($(loc.idx)) does not match"))
    return loc
end

"""
    resolve_ante(loc, seq, predicate) -> Ante

Resolve an antecedent locator against a sequent using a predicate.
  - `First()`: search for the first matching formula in the antecedent.
  - `Ante(i)`: validate that the formula at index `i` matches the predicate.
"""
function resolve_ante(::First, seq::Sequent, predicate::Function)
    idx = findfirst(predicate, seq.antecedent)
    idx === nothing && throw(TacticFailure("No matching formula in antecedent"))
    return Ante(idx)
end

function resolve_ante(loc::Ante, seq::Sequent, predicate::Function)
    1 <= loc.idx <= length(seq.antecedent) ||
        throw(TacticFailure("Ante index $(loc.idx) out of bounds ($(length(seq.antecedent)) in antecedent)"))
    predicate(seq.antecedent[loc.idx]) ||
        throw(TacticFailure("Formula at Ante($(loc.idx)) does not match"))
    return loc
end

# ══════════════════════════════════════════════════════════════════════════════
#                              TACTIC
# ══════════════════════════════════════════════════════════════════════════════

abstract type Tactic end

function (t::Tactic)(p::Derivation)
    idx = t.subgoal_idx
    if idx !== nothing
        return t(p, idx)
    end
    # Search mode: try each open subgoal, last-to-first
    for i in length(p.assumptions):-1:1
        try
            return t(p, i)
        catch e
            e isa TacticFailure || rethrow()
        end
    end
    throw(TacticFailure("No subgoal accepts tactic"))
end

Base.:(|>)(p::Derivation, t::Tactic) = t(p)::Derivation

# ══════════════════════════════════════════════════════════════════════════════
#                           TACTIC FAILURE
# ══════════════════════════════════════════════════════════════════════════════

struct TacticFailure <: Exception
    reason::String
end

Base.showerror(io::IO, e::TacticFailure) = print(io, "TacticFailure: ", e.reason)

# ══════════════════════════════════════════════════════════════════════════════
#                             EXECUTE
# ══════════════════════════════════════════════════════════════════════════════

"""
    execute(t::T, p::Derivation, subgoal_idx::Int) -> Derivation

Implement this for each concrete tactic `T`.  Called by the generated
callable with bounds-checked `subgoal_idx`.  The current sequent is
`p.assumptions[subgoal_idx]`.

Throw `TacticFailure(reason)` on failure — the stack trace points
directly at your code.
"""
function execute end

# ══════════════════════════════════════════════════════════════════════════════
#                            @tactic MACRO
# ══════════════════════════════════════════════════════════════════════════════

"""
    @tactic Name(field::Type=default, ...)

Generate:
1. `struct Name <: Tactic` with declared fields + `subgoal_idx::Union{Int,Nothing}`.
2. `(t::Name)(p, subgoal_idx)` — bounds check, then `execute(t, p, subgoal_idx)`.
3. `name(args...; kw...)` — snake_case factory (defaults `subgoal_idx=1`).
4. `Base.show`.

The struct constructor (`Name(...)`) defaults `subgoal_idx` to `nothing`
(strategy template).  The factory (`name(...)`) defaults to `1` (interactive).

Then implement `Tactics.execute(t::Name, p, subgoal_idx)` as a plain function.
"""
macro tactic(signature)
    if signature isa Symbol
        struct_name = signature
        field_exprs = []
    elseif Meta.isexpr(signature, :call)
        struct_name = signature.args[1]
        field_exprs = signature.args[2:end]
    else
        throw(ArgumentError("@tactic: expected `Name` or `Name(fields...)`, got $signature"))
    end

    tactic_sym = QuoteNode(struct_name)
    factory_name = Symbol(_to_snake_case(string(struct_name)))

    # Parse fields
    field_names, field_types, field_defaults = Symbol[], Any[], Any[]
    for fe in field_exprs
        if Meta.isexpr(fe, :kw)
            decl, default = fe.args
            fn, ft = _parse_typed_name(decl)
            push!(field_names, fn)
            push!(field_types, ft)
            push!(field_defaults, default)
        elseif Meta.isexpr(fe, :(::))
            fn, ft = _parse_typed_name(fe)
            push!(field_names, fn)
            push!(field_types, ft)
            push!(field_defaults, nothing)
        else
            throw(ArgumentError("@tactic: cannot parse field: $fe"))
        end
    end

    # Struct fields
    struct_fields = [:($(n)::$(t)) for (n, t) in zip(field_names, field_types)]
    push!(struct_fields, :(subgoal_idx::Union{Int,Nothing}))

    # Factory signature: defaults subgoal_idx=1 for interactive use
    pos_args = Any[]
    kw_args = Any[Expr(:kw, :(subgoal_idx::Union{Int,Nothing}), 1)]
    for (n, t, d) in zip(field_names, field_types, field_defaults)
        if d === nothing
            push!(pos_args, :($(n)::$(t)))
        else
            push!(kw_args, Expr(:kw, :($(n)::$(t)), d))
        end
    end

    ctor_args = vcat(field_names, [:subgoal_idx])

    # Template constructor: required positional args only, all optional = nothing
    template_typed = Any[]
    template_call = Any[]
    for i in eachindex(field_names)
        if field_defaults[i] === nothing  # required field (no default)
            push!(template_typed, :($(field_names[i])::$(field_types[i])))
            push!(template_call, field_names[i])
        else  # optional field
            push!(template_call, nothing)
        end
    end
    push!(template_call, nothing)  # subgoal_idx = nothing

    return esc(quote
        struct $struct_name <: Tactics.Tactic
            $(struct_fields...)
        end

        function (t::$struct_name)(p::Derivation, subgoal_idx::Int)
            n = length(p.assumptions)
            1 <= subgoal_idx <= n || throw(Tactics.TacticFailure(
                "Subgoal $subgoal_idx out of bounds ($n open)"))
            Tactics.execute(t, p, subgoal_idx)
        end

        # Template constructor: defaults optional fields + subgoal_idx to nothing
        $struct_name($(template_typed...)) = $struct_name($(template_call...))

        $factory_name($(pos_args...); $(kw_args...)) =
            $struct_name($(ctor_args...))

        Base.show(io::IO, ::$struct_name) = print(io, $(string(factory_name)))
    end)
end

# ── helpers (expansion-time) ─────────────────────────────────────────────────

function _to_snake_case(s::AbstractString)
    buf = IOBuffer()
    for (i, c) in enumerate(s)
        isuppercase(c) && i > 1 && write(buf, '_')
        write(buf, lowercase(c))
    end
    String(take!(buf))
end

function _parse_typed_name(expr)
    Meta.isexpr(expr, :(::)) && length(expr.args) == 2 ||
        throw(ArgumentError("@tactic: expected `name::Type`, got $expr"))
    (expr.args[1], expr.args[2])
end

end # module Tactics
