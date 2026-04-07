# ═══════════════════════════════════════════════════════════════════════════════
#                         EXPRESSION WALKERS MODULE
# ═══════════════════════════════════════════════════════════════════════════════
#
# Generic traversal utilities for terms and formulas.
# This module provides:
#   - children: Get immediate child expressions
#   - reconstruct: Build new expression with different children
#   - transform: Bottom-up tree transformation
#   - fold: Reduce over all nodes
#   - formula_kind / operands: Uniform API for derived formulas
# ═══════════════════════════════════════════════════════════════════════════════

module Walkers

using ..Kernel

export children, reconstruct, transform, fold
export find_subterm, find_subterm_formula
export formula_kind, operands, logical_reconstruct, primitive_kind
export apply_context, path_context
export free_variables
# ─────────────────────────────────────────────────────────────────────────────
#                         CHILDREN
# ─────────────────────────────────────────────────────────────────────────────

"""
    children(expr) -> Tuple

Return immediate child terms/formulas of an expression.
Leaf nodes (Variable, Constant, Hole) return empty tuple.
"""
children(::Variable) = ()
children(::Constant) = ()
children(::Hole) = ()
children(t::Sum) = (t.left, t.right)
children(t::Difference) = (t.left, t.right)
children(t::Product) = (t.left, t.right)
children(t::Division) = (t.left, t.right)
children(t::Power) = (t.base, t.exponent)
children(t::FunctionApplication) = t.arguments

# Formula children
children(f::LessThan) = (f.left, f.right)
children(f::Equals) = (f.left, f.right)
children(f::Not) = (f.formula,)
children(f::Implies) = (f.left, f.right)
children(f::Forall) = (f.body,)  # variable binding is metadata, not a child
children(f::PredicateApplication) = f.arguments

# ─────────────────────────────────────────────────────────────────────────────
#                         RECONSTRUCT
# ─────────────────────────────────────────────────────────────────────────────

"""
    reconstruct(expr, new_children...) -> typeof(expr)

Create a new expression of the same type with different children.
The number of children must match the original.
"""
reconstruct(v::Variable,) = v
reconstruct(c::Constant,) = c
reconstruct(h::Hole,) = h
reconstruct(::Sum, left, right) = Sum(left, right)
reconstruct(::Difference, left, right) = Difference(left, right)
reconstruct(::Product, left, right) = Product(left, right)
reconstruct(::Division, left, right) = Division(left, right)
reconstruct(::Power, base, exp) = Power(base, exp)
reconstruct(t::FunctionApplication, args...) = FunctionApplication(t.symbol, args)

# Formula reconstruct
reconstruct(::LessThan, left, right) = LessThan(left, right)
reconstruct(::Equals, left, right) = Equals(left, right)
reconstruct(::Not, f) = Not(f)
reconstruct(::Implies, left, right) = Implies(left, right)
reconstruct(f::Forall, body) = Forall(f.variable, body)
reconstruct(p::PredicateApplication, args...) = PredicateApplication(p.symbol, args)

# ─────────────────────────────────────────────────────────────────────────────
#                         TRANSFORM
# ─────────────────────────────────────────────────────────────────────────────

"""
    transform(f, expr)

Apply function f to each node bottom-up.
Children are transformed first, then f is applied to the reconstructed parent.

Example: transform(e -> e isa Constant ? Constant(e.value + 1) : e, term)
"""
function transform(f, expr)
    cs = children(expr)
    if isempty(cs)
        return f(expr)
    end
    new_children = map(c -> transform(f, c), cs)
    f(reconstruct(expr, new_children...))
end



# ─────────────────────────────────────────────────────────────────────────────
#                         FOLD
# ─────────────────────────────────────────────────────────────────────────────

"""
    fold(f, init, expr)

Reduce over all nodes in pre-order (parent before children).
f(acc, node) is called for each node.

Example: fold((acc, e) -> e isa Variable ? acc + 1 : acc, 0, term)  # count variables
"""
function fold(f, init, expr)
    acc = f(init, expr)
    for c in children(expr)
        acc = fold(f, acc, c)
    end
    acc
end

# ─────────────────────────────────────────────────────────────────────────────
#                       FIND_SUBTERM
# ─────────────────────────────────────────────────────────────────────────────

"""
    find_subterm(pred, term::Term) -> Union{Tuple{Any, Term}, Nothing}

Walk `term` depth-first, calling `pred(t)` at each subterm.
If `pred` returns non-`nothing`, stop and return `(result, context)` where
`context` has `Hole(1)` at the matched position.

This is the general form — `unify_subterm` is the special case where
`pred = t -> unify(pattern, t)`.
"""
function find_subterm(pred, term::Term)
    result = pred(term)
    result !== nothing && return (result, Hole(1))

    cs = children(term)
    for (i, c) in enumerate(cs)
        inner = find_subterm(pred, c)
        if inner !== nothing
            val, ctx = inner
            return (val, reconstruct(term, cs[1:i-1]..., ctx, cs[i+1:end]...))
        end
    end
    nothing
end

"""
    find_subterm_formula(pred, formula::Formula) -> Union{Tuple{Any, Formula}, Nothing}

Walk `formula` depth-first through its logical structure, calling `pred(t)` on
each term-level subterm.  Returns `(result, formula_context)` where the context
has `Hole(1)` at the matched position, or `nothing`.

Uses `formula_kind`/`operands`/`logical_reconstruct` so that derived connectives
(Equals, And, Or, …) are handled correctly.
"""
function find_subterm_formula(pred, formula::Formula)
    kind = formula_kind(formula)
    ops = operands(formula)

    for (idx, op) in enumerate(ops)
        (kind in (:forall, :exists) && idx == 1) && continue

        inner = if op isa Formula
            find_subterm_formula(pred, op)
        elseif op isa Term
            find_subterm(pred, op)
        else
            nothing
        end

        if inner !== nothing
            val, ctx = inner
            new_ops = ntuple(j -> j == idx ? ctx : ops[j], length(ops))
            return (val, logical_reconstruct(kind, formula, new_ops...))
        end
    end
    nothing
end

# ─────────────────────────────────────────────────────────────────────────────
#                    DERIVED FORMULA RECOGNITION
#      Uniform API for both primitive and derived formula connectives
# ─────────────────────────────────────────────────────────────────────────────

"""
    formula_kind(f::Formula) -> Symbol

Return a symbol describing the logical structure of the formula.
Recognizes both primitive types and derived connectives:

**Primitives:** `:lt`, `:not`, `:implies`, `:forall`, `:predicate`
**Derived:** `:and`, `:or`, `:exists`, `:iff`, `:equals`, `:le`

Note: A formula that looks like `Not(Implies(a, Not(b)))` will be recognized 
as `:and`, not `:not`. Use `primitive_kind` if you need the underlying structure.
"""
function formula_kind(f::Formula)
    # Check derived forms first, most specific before general
    # Order matters: le/iff are special cases of And or Not, so check them first
    # Note: Equals is now a primitive type, handled by primitive_kind fallthrough
    _is_le(f) && return :le
    _is_iff(f) && return :iff
    _is_and(f) && return :and
    _is_or(f) && return :or
    _is_exists(f) && return :exists

    # Fall through to primitives
    primitive_kind(f)
end

"""
    primitive_kind(f::Formula) -> Symbol

Return the primitive type of a formula, ignoring derived structure.
Always returns: `:lt`, `:equals`, `:not`, `:implies`, `:forall`, or `:predicate`.
"""
primitive_kind(::LessThan) = :lt
primitive_kind(::Equals) = :equals
primitive_kind(::Not) = :not
primitive_kind(::Implies) = :implies
primitive_kind(::Forall) = :forall
primitive_kind(::PredicateApplication) = :predicate

"""
    operands(f::Formula) -> Tuple

Return the logical operands of a formula.
Works uniformly for both primitive and derived connectives:

```julia
operands(And(a, b))     # -> (a, b), even though it's stored as Not(Implies(a, Not(b)))
operands(Implies(a, b)) # -> (a, b)
operands(Not(a))        # -> (a,)
operands(Forall(x, p))  # -> (x, p)  # includes the variable
```
"""
function operands(f::Formula)
    k = formula_kind(f)

    # Derived binary connectives
    k == :and && return _and_operands(f)
    k == :or && return _or_operands(f)
    k == :iff && return _iff_operands(f)
    k == :le && return _le_operands(f)
    k == :exists && return _exists_operands(f)

    # Primitives
    k == :equals && return (f.left, f.right)
    k == :lt && return (f.left, f.right)
    k == :not && return (f.formula,)
    k == :implies && return (f.left, f.right)
    k == :forall && return (f.variable, f.body)
    k == :predicate && return f.arguments

    error("Unknown formula kind: $k")
end

"""
    logical_reconstruct(kind::Symbol, f::Formula, new_operands...) -> Formula

Rebuild a formula from its logical kind and new operands.
Inverse of `operands`: if `ops = operands(f)` and `k = formula_kind(f)`,
then `logical_reconstruct(k, f, ops...)` produces a formula equivalent to `f`.

The original formula `f` is passed for metadata extraction
(e.g., the predicate symbol for `:predicate`).
"""
function logical_reconstruct(kind::Symbol, f::Formula, ops...)
    kind == :equals && return Equals(ops...)
    kind == :lt && return LessThan(ops...)
    kind == :not && return Not(ops...)
    kind == :implies && return Implies(ops...)
    kind == :forall && return Forall(ops...)
    kind == :predicate && return PredicateApplication(f.symbol, ops)
    # Defined connectives — inlined so Walkers doesn't depend on Syntax
    kind == :le && return Not(LessThan(ops[2], ops[1]))
    kind == :and && return Not(Implies(ops[1], Not(ops[2])))
    kind == :or && return Implies(Not(ops[1]), ops[2])
    kind == :iff && let a = ops[1], b = ops[2]
        Not(Implies(Implies(a, b), Not(Implies(b, a))))
    end
    kind == :exists && return Not(Forall(ops[1], Not(ops[2])))
    error("Unknown formula kind: $kind")
end

# ─────────────────────────────────────────────────────────────────────────────
#                    Pattern Recognizers (internal)
# ─────────────────────────────────────────────────────────────────────────────

# And: Not(Implies(a, Not(b)))
_is_and(f::Not) = f.formula isa Implies && f.formula.right isa Not
_is_and(::Formula) = false
_and_operands(f::Not) = (f.formula.left, f.formula.right.formula)

# Or: Implies(Not(a), b)
_is_or(f::Implies) = f.left isa Not
_is_or(::Formula) = false
_or_operands(f::Implies) = (f.left.formula, f.right)

# Exists: Not(Forall(x, Not(p)))
_is_exists(f::Not) = f.formula isa Forall && f.formula.body isa Not
_is_exists(::Formula) = false
_exists_operands(f::Not) = (f.formula.variable, f.formula.body.formula)

# Iff: And(Implies(a, b), Implies(b, a)) = Not(Implies(Implies(a,b), Not(Implies(b,a))))
function _is_iff(f::Not)
    _is_and(f) || return false
    left, right = _and_operands(f)
    left isa Implies && right isa Implies || return false
    left.left == right.right && left.right == right.left
end
_is_iff(::Formula) = false
_iff_operands(f::Not) = (_and_operands(f)[1].left, _and_operands(f)[1].right)

# LessOrEqual: Not(LessThan(b, a)) — a ≤ b
function _is_le(f::Not)
    f.formula isa LessThan
end
_is_le(::Formula) = false
_le_operands(f::Not) = (f.formula.right, f.formula.left)  # a ≤ b = Not(LessThan(b, a)) → (a, b)

# ─────────────────────────────────────────────────────────────────────────────
#                         APPLY CONTEXT
# ─────────────────────────────────────────────────────────────────────────────

"""
    apply_context(ctx::Term, args::Term...) -> Term

Apply a term context by replacing each `Hole(i)` with `args[i]`.

Example:
    ctx = Sum(Hole(1), Variable("y"))  # represents □ + y
    apply_context(ctx, Variable("x"))  # returns x + y
"""
function apply_context end

apply_context(c::Constant, args::Term...) = c
apply_context(v::Variable, args::Term...) = v

function apply_context(h::Hole, args::Term...)
    1 <= h.index <= length(args) || throw(BoundsError(args, h.index))
    args[h.index]
end

function apply_context(app::FunctionApplication, args::Term...)
    FunctionApplication(app.symbol, Tuple(apply_context(arg, args...) for arg in app.arguments))
end

function apply_context(t::Sum, args::Term...)
    Sum(apply_context(t.left, args...), apply_context(t.right, args...))
end

function apply_context(t::Difference, args::Term...)
    Difference(apply_context(t.left, args...), apply_context(t.right, args...))
end

function apply_context(t::Product, args::Term...)
    Product(apply_context(t.left, args...), apply_context(t.right, args...))
end

function apply_context(t::Division, args::Term...)
    Division(apply_context(t.left, args...), apply_context(t.right, args...))
end

function apply_context(t::Power, args::Term...)
    Power(apply_context(t.base, args...), t.exponent)
end

"""
    path_context(expr::Union{Term,Formula}, path::Vector{Int}) -> (HoleContext, Focus)

Traverse `expr` following `path` (a list of child indices).
Returns the formula/term with a `Hole(1)` replacing the focused node, and the focused node itself.
"""
function path_context(expr::Union{Term,Formula}, path::Vector{Int})
    if isempty(path)
        return Hole(1), expr
    end

    idx = path[1]

    if expr isa Formula
        kind = formula_kind(expr)
        ops = Any[operands(expr)...]
        hole_ctx, focus = path_context(ops[idx], path[2:end])
        ops[idx] = hole_ctx
        return logical_reconstruct(kind, expr, ops...), focus
    else
        args = Any[children(expr)...]
        hole_ctx, focus = path_context(args[idx], path[2:end])
        args[idx] = hole_ctx
        return reconstruct(expr, args...), focus
    end
end

"""
    all_matches_term(pred, term::Term) -> Vector{Tuple{Any, Term}}

Find all subterms matching `pred` and return their results and contexts.
"""
function all_matches_term(pred, term::Term)
    results = []
    res = pred(term)
    if res !== nothing
        push!(results, (res, Hole(1)))
    end
    cs = children(term)
    for (i, c) in enumerate(cs)
        for (inner_res, inner_ctx) in all_matches_term(pred, c)
            full_ctx = reconstruct(term, cs[1:i-1]..., inner_ctx, cs[i+1:end]...)
            push!(results, (inner_res, full_ctx))
        end
    end
    return results
end

"""
    all_matches_formula(pred, formula::Formula) -> Vector{Tuple{Any, Formula}}

Find all subterms matching `pred` within a formula and return their results and contexts.
"""
function all_matches_formula(pred, formula::Formula)
    kind = formula_kind(formula)
    ops = operands(formula)
    results = []
    for (idx, op) in enumerate(ops)
        inner_matches = if op isa Formula
            all_matches_formula(pred, op)
        elseif op isa Term
            all_matches_term(pred, op)
        else
            ()
        end
        for (res, ctx) in inner_matches
            new_ops = ntuple(j -> j == idx ? ctx : ops[j], length(ops))
            push!(results, (res, logical_reconstruct(kind, formula, new_ops...)))
        end
    end
    return results
end


"""
    free_variables(expr) -> Vector{Variable}

Compute the free variables of a term or formula.
"""
function free_variables end

# --- Terms ---
free_variables(::Constant)::Vector{Variable} = Variable[]
free_variables(::Hole) = Variable[]  # Holes are not variables
free_variables(v::Variable) = Variable[v]

function free_variables(app::FunctionApplication)::Vector{Variable}
    isempty(app.arguments) && return Variable[]
    unique(reduce(vcat, free_variables.(app.arguments)))
end

# --- Arithmetic Terms ---
function free_variables(t::Sum)::Vector{Variable}
    unique([free_variables(t.left)..., free_variables(t.right)...])
end

function free_variables(t::Difference)::Vector{Variable}
    unique([free_variables(t.left)..., free_variables(t.right)...])
end

function free_variables(t::Product)::Vector{Variable}
    unique([free_variables(t.left)..., free_variables(t.right)...])
end

function free_variables(t::Division)::Vector{Variable}
    unique([free_variables(t.left)..., free_variables(t.right)...])
end

function free_variables(t::Power)::Vector{Variable}
    free_variables(t.base)
end

# --- Formulas ---
function free_variables(lt::LessThan)::Vector{Variable}
    unique([free_variables(lt.left)..., free_variables(lt.right)...])
end

function free_variables(eq::Equals)::Vector{Variable}
    unique([free_variables(eq.left)..., free_variables(eq.right)...])
end

function free_variables(app::PredicateApplication)::Vector{Variable}
    isempty(app.arguments) && return Variable[]
    unique(reduce(vcat, free_variables.(app.arguments)))
end

function free_variables(neg::Not)::Vector{Variable}
    free_variables(neg.formula)
end

function free_variables(impl::Implies)::Vector{Variable}
    unique([free_variables(impl.left)..., free_variables(impl.right)...])
end

function free_variables(fa::Forall)::Vector{Variable}
    filter(v -> v != fa.variable, free_variables(fa.body))
end

function free_variables(seq::Sequent)::Set{Variable}
    ante_vars = isempty(seq.antecedent) ? Variable[] : reduce(vcat, free_variables.(seq.antecedent))
    cons_vars = isempty(seq.consequent) ? Variable[] : reduce(vcat, free_variables.(seq.consequent))
    Set{Variable}(vcat(ante_vars, cons_vars))
end

end # module Walkers

