module Kernel

# ═══════════════════════════════════════════════════════════════════════════════
#                              SECTION 1: TERMS
# ═══════════════════════════════════════════════════════════════════════════════

"""
    Term

Abstract base type for all terms in the logic.
"""
abstract type Term end

"""
    Variable <: Term

A logical variable that can be substituted.
"""
struct Variable <: Term
    name::String
end

"""
    Constant <: Term

A numeric constant represented as an exact rational number.
"""
struct Constant <: Term
    value::Rational{BigInt}

    Constant(n::Integer) = new(Rational{BigInt}(n))
    Constant(r::Rational) = new(Rational{BigInt}(r))
    Constant(r::Rational{BigInt}) = new(r)
end

"""
    FunctionSymbol

A function symbol (not a term itself). Used to build FunctionApplication terms.
"""
struct FunctionSymbol
    name::String
end

"""
    FunctionApplication <: Term

Application of a function symbol to term arguments.
"""
struct FunctionApplication <: Term
    symbol::FunctionSymbol
    arguments::NTuple{N,Term} where N
end

(fs::FunctionSymbol)(args::Term...) = FunctionApplication(fs, args)

# ─────────────────────────────────────────────────────────────────────────────
#                         Arithmetic Terms
# ─────────────────────────────────────────────────────────────────────────────

"""
    Sum <: Term

Sum of two terms: `left + right`.
"""
struct Sum <: Term
    left::Term
    right::Term
end

"""
    Difference <: Term

Difference of two terms: `left - right`.
"""
struct Difference <: Term
    left::Term
    right::Term
end

"""
    Product <: Term

Product of two terms: `left * right`.
"""
struct Product <: Term
    left::Term
    right::Term
end

"""
    Division <: Term

Division of two terms: `left / right`.
"""
struct Division <: Term
    left::Term
    right::Term
end

"""
    Power <: Term

Power: `base^exponent` where exponent is a constant.
"""
struct Power <: Term
    base::Term
    exponent::Constant
end

"""
    Hole <: Term

A placeholder in a term context, representing "where argument i goes".
Used for substituting n-ary schematic function symbols with contexts.

Example: The context `□ + y` is represented as `Sum(Hole(1), y)`.
Applying this context to term `t` yields `Sum(t, y)`.
"""
struct Hole <: Term
    index::Int

    function Hole(index::Int)
        index > 0 || throw(ArgumentError("Hole index must be positive"))
        new(index)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#                     SECTION 2: FORMULAS (MINIMAL BASIS)
#                         Primitives: ¬, →, ∀, and atomic
# ═══════════════════════════════════════════════════════════════════════════════

"""
    Formula

Abstract base type for all formulas.
"""
abstract type Formula end

# ─────────────────────────────────────────────────────────────────────────────
#                            Atomic Formulas
# ─────────────────────────────────────────────────────────────────────────────

"""
    PredicateSymbol

A predicate symbol. Used to build PredicateApplication.
"""
struct PredicateSymbol
    name::String
end

"""
    PredicateApplication <: Formula

Application of a predicate symbol to term arguments.
"""
struct PredicateApplication <: Formula
    symbol::PredicateSymbol
    arguments::NTuple{N,Term} where N
end

(ps::PredicateSymbol)(args::Term...) = PredicateApplication(ps, args)

"""
    LessThan <: Formula

Strict less-than comparison: `left < right`. PRIMITIVE.
"""
struct LessThan <: Formula
    left::Term
    right::Term
end

"""
    Equals <: Formula

Equality: `a = b`. PRIMITIVE.
"""
struct Equals <: Formula
    left::Term
    right::Term
end

# ─────────────────────────────────────────────────────────────────────────────
#                    Primitive Connectives: ¬, →, ∀
# ─────────────────────────────────────────────────────────────────────────────

"""
    Not <: Formula

Logical negation: `¬A`. PRIMITIVE.
"""
struct Not <: Formula
    formula::Formula
end

"""
    Implies <: Formula

Logical implication: `A → B`. PRIMITIVE.
"""
struct Implies <: Formula
    left::Formula
    right::Formula
end

"""
    Forall <: Formula

Universal quantification: `∀x. P`. PRIMITIVE.
"""
struct Forall <: Formula
    variable::Variable
    body::Formula
end


# ═══════════════════════════════════════════════════════════════════════════════
#                         SECTION 3: SYNTACTIC SIDE CONDITIONS
# ═══════════════════════════════════════════════════════════════════════════════
function has_clash(expr::Union{Term,Formula}, taboo::Set{Variable})
    return _has_clash(expr, taboo, Variable[])
end

_has_clash(::Constant, _, _) = false
_has_clash(::Hole, _, _) = false
_has_clash(v::Variable, taboo::Set{Variable}, internal_bound::Vector{Variable}) = v ∈ taboo && v ∉ internal_bound
_has_clash(t::FunctionApplication, taboo::Set{Variable}, internal_bound::Vector{Variable}) = any(_has_clash(arg, taboo, internal_bound) for arg in t.arguments)
_has_clash(t::Sum, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(t.left, taboo, internal_bound) || _has_clash(t.right, taboo, internal_bound)
_has_clash(t::Difference, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(t.left, taboo, internal_bound) || _has_clash(t.right, taboo, internal_bound)
_has_clash(t::Division, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(t.left, taboo, internal_bound) || _has_clash(t.right, taboo, internal_bound)
_has_clash(t::Product, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(t.left, taboo, internal_bound) || _has_clash(t.right, taboo, internal_bound)
_has_clash(t::Power, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(t.base, taboo, internal_bound)

_has_clash(fml::PredicateApplication, taboo::Set{Variable}, internal_bound::Vector{Variable}) = any(_has_clash(arg, taboo, internal_bound) for arg in fml.arguments)
_has_clash(fml::LessThan, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(fml.left, taboo, internal_bound) || _has_clash(fml.right, taboo, internal_bound)
_has_clash(fml::Equals, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(fml.left, taboo, internal_bound) || _has_clash(fml.right, taboo, internal_bound)
_has_clash(fml::Not, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(fml.formula, taboo, internal_bound)
_has_clash(fml::Implies, taboo::Set{Variable}, internal_bound::Vector{Variable}) = _has_clash(fml.left, taboo, internal_bound) || _has_clash(fml.right, taboo, internal_bound)

function _has_clash(fa::Forall, taboo::Set{Variable}, internal_bound::Vector{Variable})
    push!(internal_bound, fa.variable)
    found = _has_clash(fa.body, taboo, internal_bound)
    pop!(internal_bound)
    return found
end



# ═══════════════════════════════════════════════════════════════════════════════
#                          SECTION 4: SUBSTITUTION
# ═══════════════════════════════════════════════════════════════════════════════

# ─────────────────────────────────────────────────────────────────────────────
#   Renaming (internal, for quantifier rules)
#   Capture-avoiding renaming of Variables → Terms
# ─────────────────────────────────────────────────────────────────────────────

struct Renaming
    old::Variable
    new::Variable
end

function rename end

# --- Terms ---
rename(c::Constant, ::Renaming)::Union{Term,Formula} = c
rename(h::Hole, ::Renaming)::Union{Term,Formula} = h  # Holes are not affected by renaming

function rename(v::Variable, ρ::Renaming)
    v == ρ.old ? ρ.new : v
end

function rename(app::FunctionApplication, ρ::Renaming)::Union{Term,Formula}
    FunctionApplication(app.symbol, Tuple(rename(arg, ρ) for arg in app.arguments))
end

# --- Arithmetic Terms ---
function rename(t::Sum, ρ::Renaming)::Union{Term,Formula}
    Sum(rename(t.left, ρ), rename(t.right, ρ))
end

function rename(t::Difference, ρ::Renaming)::Union{Term,Formula}
    Difference(rename(t.left, ρ), rename(t.right, ρ))
end

function rename(t::Product, ρ::Renaming)::Union{Term,Formula}
    Product(rename(t.left, ρ), rename(t.right, ρ))
end

function rename(t::Division, ρ::Renaming)::Union{Term,Formula}
    Division(rename(t.left, ρ), rename(t.right, ρ))
end

function rename(t::Power, ρ::Renaming)::Union{Term,Formula}
    Power(rename(t.base, ρ), t.exponent)
end

# --- Formulas ---
function rename(lt::LessThan, ρ::Renaming)::Union{Term,Formula}
    LessThan(rename(lt.left, ρ), rename(lt.right, ρ))
end

function rename(eq::Equals, ρ::Renaming)::Union{Term,Formula}
    Equals(rename(eq.left, ρ), rename(eq.right, ρ))
end

function rename(app::PredicateApplication, ρ::Renaming)::Union{Term,Formula}
    PredicateApplication(app.symbol, Tuple(rename(arg, ρ) for arg in app.arguments))
end

function rename(neg::Not, ρ::Renaming)::Union{Term,Formula}
    Not(rename(neg.formula, ρ))
end

function rename(impl::Implies, ρ::Renaming)::Union{Term,Formula}
    Implies(rename(impl.left, ρ), rename(impl.right, ρ))
end

function rename(fa::Forall, ρ::Renaming)::Union{Term,Formula}
    # Shadowing: if the bound variable is ρ.old, the renaming stops
    if fa.variable == ρ.old
        return fa
    end
    # Capture check: if we are renaming something to ρ.new, it will be captured
    if fa.variable == ρ.new
        error("Renaming $(ρ.old) to $(ρ.new) would capture bound variable $(fa.variable)")
    end
    # Recurse
    Forall(fa.variable, rename(fa.body, ρ))
end

# ─────────────────────────────────────────────────────────────────────────────
#   Substitution (main API for axiom instantiation)
#   Uniform substitution following Platzer's uniform substitution calculus.
#   Maps FunctionSymbol → Term  and  PredicateSymbol → Formula.
# ─────────────────────────────────────────────────────────────────────────────

"""
    Substitution

Uniform substitution mapping:
  - `FunctionSymbol → Term`  for instantiating schematic term placeholders
  - `PredicateSymbol → Formula`  for instantiating schematic predicate placeholders
  - `Int → Term`  (hole bindings) for internal context application

Following Platzer's definition:
  σ(f(θ)) = {· ↦ σθ}∅ σf(·)   with FV(σf(·)) ∩ U = ∅
  σ(p(θ)) = {· ↦ σθ}∅ σp(·)   with FV(σp(·)) ∩ U = ∅

The replacement for an n-ary symbol uses `Hole(i)` to refer to argument i.
Nullary symbols (0 arguments) map to plain terms/formulas.

**Mixing invariant**: A Substitution may contain *either* function/predicate
bindings *or* hole bindings, but never both. This is enforced at construction.
Hole bindings are used internally to apply contexts through the full
substitution machinery (with taboo tracking), preventing variable capture.
"""
abstract type Substitution end

struct SymbolSubstitution <: Substitution
    bindings::Base.ImmutableDict{FunctionSymbol,Term}
    pred_bindings::Base.ImmutableDict{PredicateSymbol,Formula}
end

struct HoleSubstitution <: Substitution
    hole_bindings::Base.ImmutableDict{Int,Term}
end

# A clean one-liner to build ImmutableDicts safely
_freeze(::Type{K}, ::Type{V}, itr) where {K,V} = foldl(Base.ImmutableDict, itr; init=Base.ImmutableDict{K,V}())

Substitution() = SymbolSubstitution(
    Base.ImmutableDict{FunctionSymbol,Term}(),
    Base.ImmutableDict{PredicateSymbol,Formula}(),
)

Substitution(bindings::AbstractDict{FunctionSymbol,Term}, pred_bindings::AbstractDict{PredicateSymbol,Formula}) =
    SymbolSubstitution(_freeze(FunctionSymbol, Term, bindings), _freeze(PredicateSymbol, Formula, pred_bindings))

Substitution(bindings::AbstractDict{FunctionSymbol,Term}) =
    Substitution(bindings, Dict{PredicateSymbol,Formula}())

Substitution(pred_bindings::AbstractDict{PredicateSymbol,Formula}) =
    Substitution(Dict{FunctionSymbol,Term}(), pred_bindings)

function Substitution(pairs::Pair{Int,<:Term}...)
    HoleSubstitution(_freeze(Int, Term, pairs))
end

Substitution(bindings::AbstractDict{Int,Term}) =
    HoleSubstitution(_freeze(Int, Term, bindings))

function Substitution(pairs::Union{Pair{FunctionSymbol,<:Term},Pair{PredicateSymbol,<:Formula}}...)
    func_pairs = Pair{FunctionSymbol,Term}[]
    pred_pairs = Pair{PredicateSymbol,Formula}[]
    for pair in pairs
        if pair.first isa FunctionSymbol
            push!(func_pairs, pair)
        else
            push!(pred_pairs, pair)
        end
    end
    SymbolSubstitution(_freeze(FunctionSymbol, Term, func_pairs), _freeze(PredicateSymbol, Formula, pred_pairs))
end
"""
    substitute(expr, σ::Substitution)

Apply uniform substitution σ using Platzer's uniform substitution approach.
Tracks "taboo" bound variables to detect inadmissible substitutions that would
cause variable capture.

Throws ArgumentError if substitution is inadmissible (replacement term contains
a variable that would be captured by a quantifier).
"""
function substitute end

# Public interface: start with empty taboo set
substitute(fml::Formula, σ::Substitution)::Formula = _substitute(fml, σ, Set{Variable}())
substitute(t::Term, σ::Substitution)::Term = _substitute(t, σ, Set{Variable}())

# ─────────────────────────────────────────────────────────────────────────────
#                    INTERNAL SUBSTITUTION WITH TABOO SET
# ─────────────────────────────────────────────────────────────────────────────

"""
Check that expression (Term or Formula) contains no taboo variables (admissibility check).
Works for both FunctionSymbol → Term and PredicateSymbol → Formula substitutions.
"""
function _check_admissible(expr, taboo::Set{Variable}, symbol)
    if has_clash(expr, taboo)
        throw(ArgumentError(
            "Inadmissible substitution: $symbol substituted with expression containing " *
            "bound variable(s). This would cause variable capture."
        ))
    end
end


# --- Terms ---
_substitute(c::Constant, ::Substitution, ::Set{Variable})::Constant = c
_substitute(v::Variable, ::Substitution, ::Set{Variable})::Variable = v

_substitute(h::Hole, ::SymbolSubstitution, ::Set{Variable})::Hole = h

function _substitute(h::Hole, σ::HoleSubstitution, taboo::Set{Variable})::Term
    if haskey(σ.hole_bindings, h.index)
        result = σ.hole_bindings[h.index]
        _check_admissible(result, taboo, "Hole($(h.index))")
        return result
    end
    h
end

function _substitute(app::FunctionApplication, σ::SymbolSubstitution, taboo::Set{Variable})::Term
    if haskey(σ.bindings, app.symbol)
        ctx = σ.bindings[app.symbol]
        # 1. Admissibility check: FV(σf(·)) ∩ U = ∅
        _check_admissible(ctx, taboo, app.symbol)
        if isempty(app.arguments)
            # Nullary case: direct replacement
            return ctx
        else
            # N-ary case: σ(f(θ)) = {· ↦ σθ}∅ σf(·)  with FV(σf(·)) ∩ U = ∅
            # 2. Create Substitution with substituted arguments: {· ↦ σθ}
            inner_σ = HoleSubstitution(_freeze(Int, Term, (i => _substitute(arg, σ, taboo) for (i, arg) in enumerate(app.arguments))))
            # 3. Apply term context: {· ↦ σθ}∅ σf(·) — starts with empty taboo
            return _substitute(ctx, inner_σ, Set{Variable}())
        end
    end
    # Otherwise recurse into arguments
    FunctionApplication(app.symbol, Tuple(_substitute(arg, σ, taboo) for arg in app.arguments))
end

function _substitute(app::FunctionApplication, σ::HoleSubstitution, taboo::Set{Variable})::FunctionApplication
    FunctionApplication(app.symbol, Tuple(_substitute(arg, σ, taboo) for arg in app.arguments))
end

# --- Arithmetic Terms ---
_substitute(t::Sum, σ::Substitution, taboo::Set{Variable})::Sum =
    Sum(_substitute(t.left, σ, taboo), _substitute(t.right, σ, taboo))

_substitute(t::Difference, σ::Substitution, taboo::Set{Variable})::Difference =
    Difference(_substitute(t.left, σ, taboo), _substitute(t.right, σ, taboo))

_substitute(t::Product, σ::Substitution, taboo::Set{Variable})::Product =
    Product(_substitute(t.left, σ, taboo), _substitute(t.right, σ, taboo))

_substitute(t::Division, σ::Substitution, taboo::Set{Variable})::Division =
    Division(_substitute(t.left, σ, taboo), _substitute(t.right, σ, taboo))

_substitute(t::Power, σ::Substitution, taboo::Set{Variable})::Power =
    Power(_substitute(t.base, σ, taboo), t.exponent)

# --- Formulas ---
_substitute(lt::LessThan, σ::Substitution, taboo::Set{Variable})::LessThan =
    LessThan(_substitute(lt.left, σ, taboo), _substitute(lt.right, σ, taboo))

_substitute(eq::Equals, σ::Substitution, taboo::Set{Variable})::Equals =
    Equals(_substitute(eq.left, σ, taboo), _substitute(eq.right, σ, taboo))

function _substitute(app::PredicateApplication, σ::SymbolSubstitution, taboo::Set{Variable})::Formula
    if haskey(σ.pred_bindings, app.symbol)
        ctx = σ.pred_bindings[app.symbol]
        # 1. Admissibility check: FV(σp(·)) ∩ U = ∅
        _check_admissible(ctx, taboo, app.symbol)
        if isempty(app.arguments)
            # Nullary predicate: direct replacement — σ(p()) = σp
            return ctx
        else
            # 2. Create Substitution with substituted arguments: {· ↦ σθ}
            inner_σ = HoleSubstitution(_freeze(Int, Term, (i => _substitute(arg, σ, taboo) for (i, arg) in enumerate(app.arguments))))
            # 3. Apply formula context: {· ↦ σθ}∅ σp(·) — starts with empty taboo
            return _substitute(ctx, inner_σ, Set{Variable}())
        end
    end
    # No substitution for this predicate: recurse into term arguments only
    PredicateApplication(app.symbol, Tuple(_substitute(arg, σ, taboo) for arg in app.arguments))
end

function _substitute(app::PredicateApplication, σ::HoleSubstitution, taboo::Set{Variable})::PredicateApplication
    PredicateApplication(app.symbol, Tuple(_substitute(arg, σ, taboo) for arg in app.arguments))
end

_substitute(neg::Not, σ::Substitution, taboo::Set{Variable})::Not =
    Not(_substitute(neg.formula, σ, taboo))

_substitute(impl::Implies, σ::Substitution, taboo::Set{Variable})::Implies =
    Implies(_substitute(impl.left, σ, taboo), _substitute(impl.right, σ, taboo))

function _substitute(fa::Forall, σ::Substitution, taboo::Set{Variable})::Forall
    # Add bound variable to taboo set when descending into quantifier
    Forall(fa.variable, _substitute(fa.body, σ, union(taboo, Set([fa.variable]))))
end

# ═══════════════════════════════════════════════════════════════════════════════
#                        SECTION 5: EQUALITY
# ═══════════════════════════════════════════════════════════════════════════════
#
# Required for:
#   - Substitution: Variable == (and hash for Dict key)
#   - CloseRule: Formula ==
#   - ApplySubproofRule: Sequent ==
#
# ═══════════════════════════════════════════════════════════════════════════════

Base.:(==)(a::Variable, b::Variable) = a.name == b.name
Base.:(==)(a::Hole, b::Hole) = a.index == b.index
Base.:(==)(a::Constant, b::Constant) = a.value == b.value
Base.:(==)(a::FunctionSymbol, b::FunctionSymbol) = a.name == b.name
Base.:(==)(a::FunctionApplication, b::FunctionApplication) = a.symbol == b.symbol && a.arguments == b.arguments
Base.:(==)(a::Sum, b::Sum) = a.left == b.left && a.right == b.right
Base.:(==)(a::Difference, b::Difference) = a.left == b.left && a.right == b.right
Base.:(==)(a::Product, b::Product) = a.left == b.left && a.right == b.right
Base.:(==)(a::Division, b::Division) = a.left == b.left && a.right == b.right
Base.:(==)(a::Power, b::Power) = a.base == b.base && a.exponent == b.exponent

# Formulas (needed for CloseRule)
Base.:(==)(a::PredicateSymbol, b::PredicateSymbol) = a.name == b.name
Base.:(==)(a::PredicateApplication, b::PredicateApplication) = a.symbol == b.symbol && a.arguments == b.arguments
Base.:(==)(a::LessThan, b::LessThan) = a.left == b.left && a.right == b.right
Base.:(==)(a::Equals, b::Equals) = a.left == b.left && a.right == b.right
Base.:(==)(a::Not, b::Not) = a.formula == b.formula
Base.:(==)(a::Implies, b::Implies) = a.left == b.left && a.right == b.right
Base.:(==)(a::Forall, b::Forall) = a.variable == b.variable && a.body == b.body

Base.hash(v::Variable, h::UInt) = hash(v.name, hash(:Variable, h))
Base.hash(h::Hole, hh::UInt) = hash(h.index, hash(:Hole, hh))
Base.hash(fs::FunctionSymbol, h::UInt) = hash(fs.name, hash(:FunctionSymbol, h))
Base.hash(c::Constant, h::UInt) = hash(c.value, hash(:Constant, h))
Base.hash(a::FunctionApplication, h::UInt) = hash(a.arguments, hash(a.symbol, hash(:FunctionApplication, h)))
Base.hash(a::Sum, h::UInt) = hash(a.right, hash(a.left, hash(:Sum, h)))
Base.hash(a::Difference, h::UInt) = hash(a.right, hash(a.left, hash(:Difference, h)))
Base.hash(a::Product, h::UInt) = hash(a.right, hash(a.left, hash(:Product, h)))
Base.hash(a::Division, h::UInt) = hash(a.right, hash(a.left, hash(:Division, h)))
Base.hash(a::Power, h::UInt) = hash(a.exponent, hash(a.base, hash(:Power, h)))

# Formulas
Base.hash(ps::PredicateSymbol, h::UInt) = hash(ps.name, hash(:PredicateSymbol, h))
Base.hash(a::PredicateApplication, h::UInt) = hash(a.arguments, hash(a.symbol, hash(:PredicateApplication, h)))
Base.hash(a::LessThan, h::UInt) = hash(a.right, hash(a.left, hash(:LessThan, h)))
Base.hash(eq::Equals, h::UInt) = hash(eq.right, hash(eq.left, hash(:Equals, h)))
Base.hash(a::Not, h::UInt) = hash(a.formula, hash(:Not, h))
Base.hash(a::Implies, h::UInt) = hash(a.right, hash(a.left, hash(:Implies, h)))
Base.hash(a::Forall, h::UInt) = hash(a.body, hash(a.variable, hash(:Forall, h)))
# ═══════════════════════════════════════════════════════════════════════════════
#                           SECTION 6: CORE AXIOMS
# ═══════════════════════════════════════════════════════════════════════════════

# Defined helpers used to state derived connectives/comparisons in axioms.
And(left::Formula, right::Formula) = Not(Implies(left, Not(right)))
Or(left::Formula, right::Formula) = Implies(Not(left), right)
LessOrEqual(left::Term, right::Term) = Not(LessThan(right, left))

# Axiom vocabulary
const _x_sym = FunctionSymbol("_x")
const _y_sym = FunctionSymbol("_y")
const _z_sym = FunctionSymbol("_z")
const _w_sym = FunctionSymbol("_w")
const _a_sym = FunctionSymbol("_a")
const _b_sym = FunctionSymbol("_b")
const _c_sym = FunctionSymbol("_c")

const _P_sym = PredicateSymbol("_P")
const _Q_sym = PredicateSymbol("_Q")
const _C_sym = FunctionSymbol("_C")

const ZERO = Constant(0)
const ONE = Constant(1)

const _x = _x_sym()
const _y = _y_sym()
const _z = _z_sym()
const _w = _w_sym()
const _a = _a_sym()
const _b = _b_sym()
const _c = _c_sym()
const _C = (t::Term) -> _C_sym(t)

"""
    KernelAxiom

A foundational axiom of the logic.
"""
struct KernelAxiom
    formula::Formula
end

# Equality
const AX_EQ_REFL = KernelAxiom(Equals(_x, _x))

# Congruence / substitution
const AX_CONG_CONTEXT = KernelAxiom(
    Implies(Equals(_x, _y), Equals(_C_sym(_x), _C_sym(_y)))
)

const AX_CONG_PRED = KernelAxiom(
    Implies(Equals(_x, _y), Implies(_P_sym(_x), _P_sym(_y)))
)

# Strict order (<)
const AX_LT_IRREFLEXIVITY = KernelAxiom(Not(LessThan(_x, _x)))
const AX_LT_TRANS = KernelAxiom(
    Implies(And(LessThan(_x, _y), LessThan(_y, _z)), LessThan(_x, _z))
)
const AX_LT_TRICHOTOMY = KernelAxiom(
    Or(LessThan(_x, _y), Or(Equals(_x, _y), LessThan(_y, _x)))
)
const AX_LT_ADD = KernelAxiom(
    Implies(LessThan(_x, _y), LessThan(Sum(_x, _z), Sum(_y, _z)))
)
const AX_LT_MUL_POS = KernelAxiom(
    Implies(
        And(LessThan(ZERO, _z), LessThan(_x, _y)),
        LessThan(Product(_x, _z), Product(_y, _z))
    )
)

const KERNEL_ORDER_AXIOMS = [
    AX_LT_IRREFLEXIVITY, AX_LT_TRANS, AX_LT_TRICHOTOMY,
    AX_LT_ADD, AX_LT_MUL_POS
]

# Additive group
const AX_ADD_ASSO = KernelAxiom(
    Equals(Sum(Sum(_x, _y), _z), Sum(_x, Sum(_y, _z)))
)
const AX_ADD_ID = KernelAxiom(Equals(Sum(_x, ZERO), _x))
const AX_ADD_INV = KernelAxiom(Equals(Sum(_x, Product(Constant(-1), _x)), ZERO))
const AX_ADD_COMM = KernelAxiom(Equals(Sum(_x, _y), Sum(_y, _x)))

# Multiplicative group
const AX_MUL_ASSO = KernelAxiom(
    Equals(Product(Product(_x, _y), _z), Product(_x, Product(_y, _z)))
)
const AX_MUL_ID = KernelAxiom(Equals(Product(ONE, _x), _x))
const AX_MUL_INV = KernelAxiom(
    Implies(Not(Equals(_x, ZERO)), Equals(Product(_x, Division(ONE, _x)), ONE))
)
const AX_MUL_COMM = KernelAxiom(Equals(Product(_x, _y), Product(_y, _x)))

const AX_DIS = KernelAxiom(
    Equals(Product(_x, Sum(_y, _z)), Sum(Product(_x, _y), Product(_x, _z)))
)

# Difference definition: x - y = x + (-1) * y
const AX_DIFF = KernelAxiom(
    Equals(Difference(_x, _y), Sum(_x, Product(Constant(-1), _y)))
)

const KERNEL_FIELD_AXIOMS = [
    AX_ADD_ID,
    AX_MUL_ID,
    AX_MUL_COMM, AX_MUL_ASSO,
    AX_DIS,
    AX_DIFF,
]

# Core order structure
# TODO: derivable from AX_LT_TRANS, AX_LT_TRICHOTOMY, and AX_EQ_REFL
const AX_LEQ_TRANS = KernelAxiom(
    Implies(And(LessOrEqual(_x, _z), LessOrEqual(_z, _y)), LessOrEqual(_x, _y))
)

# Closure under arithmetic operations
# TODO: derivable from AX_LEQ_ADD and AX_LT_MUL_POS (scaling by -1)
const AX_LEQ_SUB = KernelAxiom(
    Implies(
        And(LessOrEqual(_x, _y), LessOrEqual(_z, _w)),
        LessOrEqual(Difference(_x, _w), Difference(_y, _z))
    )
)

# TODO: derivable from AX_LT_ADD (applied to both inequalities)
const AX_LEQ_ADD = KernelAxiom(
    Implies(
        And(LessOrEqual(_x, _y), LessOrEqual(_z, _w)),
        LessOrEqual(Sum(_x, _z), Sum(_y, _w))
    )
)

# TODO: derivable from AX_LT_TRICHOTOMY and AX_LT_MUL_POS
const AX_LEQ_SCALE_LEFT = KernelAxiom(
    Implies(
        LessOrEqual(ZERO, _z),
        Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_z, _x), Product(_z, _y)))
    )
)

# TODO: derivable from AX_LEQ_SCALE_LEFT + AX_MUL_COMM
const AX_LEQ_SCALE_RIGHT = KernelAxiom(
    Implies(
        LessOrEqual(ZERO, _z),
        Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_x, _z), Product(_y, _z)))
    )
)

# TODO: derivable from AX_LEQ_SCALE_LEFT and field operations (multiplication by -1)
const AX_LEQ_SCALE_LEFT_NEG = KernelAxiom(
    Implies(
        LessOrEqual(_z, ZERO),
        Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_z, _y), Product(_z, _x)))
    )
)

# TODO: derivable from AX_LEQ_SCALE_LEFT_NEG + AX_MUL_COMM
const AX_LEQ_SCALE_RIGHT_NEG = KernelAxiom(
    Implies(
        LessOrEqual(_z, ZERO),
        Implies(LessOrEqual(_x, _y), LessOrEqual(Product(_y, _z), Product(_x, _z)))
    )
)

# Difference-to-order bridges
# TODO: derivable from AX_LEQ_ADD (adding y to both sides)
const AX_LEQ_SUB_TO_ZERO = KernelAxiom(
    Implies(LessOrEqual(Difference(_x, _y), ZERO), LessOrEqual(_x, _y))
)

# TODO: derivable from AX_LT_ADD (adding y to both sides)
const AX_LT_SUB_TO_ZERO = KernelAxiom(
    Implies(LessThan(Difference(_x, _y), ZERO), LessThan(_x, _y))
)

# Quantifier instantiation
const _forall_x = Variable("_forall_x")
const AX_FORALL_INST = KernelAxiom(
    Implies(Forall(_forall_x, _P_sym(_forall_x)), _P_sym(_y))
)

const VALID_KERNEL_AXIOMS = Set{KernelAxiom}([
    AX_EQ_REFL,
    AX_CONG_CONTEXT,
    AX_CONG_PRED,
    AX_LT_IRREFLEXIVITY,
    AX_LT_TRANS,
    AX_LT_TRICHOTOMY,
    AX_LT_ADD,
    AX_LT_MUL_POS,
    AX_ADD_ASSO,
    AX_ADD_ID,
    AX_ADD_INV,
    AX_ADD_COMM,
    AX_MUL_ASSO,
    AX_MUL_ID,
    AX_MUL_INV,
    AX_MUL_COMM,
    AX_DIS,
    AX_DIFF,
    AX_LEQ_TRANS,
    AX_LEQ_SUB,
    AX_LEQ_ADD,
    AX_LEQ_SCALE_LEFT,
    AX_LEQ_SCALE_RIGHT,
    AX_LEQ_SCALE_LEFT_NEG,
    AX_LEQ_SCALE_RIGHT_NEG,
    AX_LEQ_SUB_TO_ZERO,
    AX_LT_SUB_TO_ZERO,
    AX_FORALL_INST,
])

# ═══════════════════════════════════════════════════════════════════════════════
#                         SECTION 7: PROOF STATE
# ═══════════════════════════════════════════════════════════════════════════════

"""
    Ante

Type-safe reference to a formula in the antecedent.
"""
struct Ante
    idx::Int

    function Ante(idx::Int)
        idx > 0 || throw(ArgumentError("Ante index must be positive"))
        new(idx)
    end
end

"""
    Cons

Type-safe reference to a formula in the consequent.
"""
struct Cons
    idx::Int

    function Cons(idx::Int)
        idx > 0 || throw(ArgumentError("Cons index must be positive"))
        new(idx)
    end
end

const SequentPosition = Union{Ante,Cons}

"""
    Sequent

A sequent Γ ⊢ Δ.
"""
struct Sequent
    antecedent::NTuple{N,Formula} where N
    consequent::NTuple{M,Formula} where M
end

Sequent(formula::Formula) = Sequent((), (formula,))

# Needed for ApplySubproofRule
Base.:(==)(a::Sequent, b::Sequent) = a.antecedent == b.antecedent && a.consequent == b.consequent

"""
    has_clash(sequent::Sequent) -> Bool

Check if the sequent contains any free variables.
"""
function has_clash(sequent::Sequent, taboo::Set{Variable})
    for formula in sequent.antecedent
        if has_clash(formula, taboo)
            return true
        end
    end
    for formula in sequent.consequent
        if has_clash(formula, taboo)
            return true
        end
    end
    return false
end

# ═══════════════════════════════════════════════════════════════════════════════
#                         SECTION 8: KERNEL RULES
#                Only rules for primitive connectives: ¬, →, ∀
# ═══════════════════════════════════════════════════════════════════════════════

# ─────────────────────────────────────────────────────────────────────────────
#                          Basic Construction Rules
# ─────────────────────────────────────────────────────────────────────────────
abstract type KernelRule end

"""
    Assume(sequent)

Create a proof state where the sequent must be proven.
"""
struct Assume <: KernelRule
    sequent::Sequent
end

"""
    AxiomRule(axiom)

Create a complete proof from a core axiom.
"""
struct AxiomRule <: KernelRule
    axiom::KernelAxiom

    function AxiomRule(axiom::KernelAxiom)
        axiom in VALID_KERNEL_AXIOMS ||
            throw(ArgumentError("AxiomRule: axiom is not in the kernel's valid axiom set"))
        new(axiom)
    end
end

struct UntrustedRule <: KernelRule
    sequent::Sequent
    tool::Symbol
end

# ─────────────────────────────────────────────────────────────────────────────
#                       Right Rules (Goal-Oriented)
# ─────────────────────────────────────────────────────────────────────────────

"""
    ImpliesRightRule(sequent, target)

→-Right: For goal `A → B`, move `A` to antecedent and prove `B`.
"""
struct ImpliesRightRule <: KernelRule
    sequent::Sequent
    target::Cons
    insert::Ante

    function ImpliesRightRule(sequent::Sequent, target::Cons, insert::Ante)
        1 <= target.idx <= length(sequent.consequent) || throw(BoundsError(sequent.consequent, target.idx))
        1 <= insert.idx <= length(sequent.antecedent) + 1 || throw(BoundsError(sequent.antecedent, insert.idx))
        goal = sequent.consequent[target.idx]
        goal isa Implies || throw(ArgumentError("ImpliesRightRule requires Implies, got $(typeof(goal))"))
        new(sequent, target, insert)
    end
end

"""
    NotRightRule(sequent, target)

¬-Right: For goal `¬A`, move `A` to antecedent (with empty consequent for that branch).
"""
struct NotRightRule <: KernelRule
    sequent::Sequent
    target::Cons
    insert::Ante

    function NotRightRule(sequent::Sequent, target::Cons, insert::Ante)
        1 <= target.idx <= length(sequent.consequent) || throw(BoundsError(sequent.consequent, target.idx))
        1 <= insert.idx <= length(sequent.antecedent) + 1 || throw(BoundsError(sequent.antecedent, insert.idx))
        goal = sequent.consequent[target.idx]
        goal isa Not || throw(ArgumentError("NotRightRule requires Not, got $(typeof(goal))"))
        new(sequent, target, insert)
    end
end

"""
    ForallRightRule(sequent, target, fresh)

∀-Right: For goal `∀x.P(x)`, prove `P(y)` where `fresh` is a variable
not free in the sequent.  The caller (tactic) generates the fresh name;
the kernel only checks freshness (soundness-critical).
"""
struct ForallRightRule <: KernelRule
    sequent::Sequent
    target::Cons
    fresh::Variable

    function ForallRightRule(sequent::Sequent, target::Cons, fresh::Variable)
        1 <= target.idx <= length(sequent.consequent) || throw(BoundsError(sequent.consequent, target.idx))
        goal = sequent.consequent[target.idx]
        goal isa Forall || throw(ArgumentError("ForallRightRule requires Forall, got $(typeof(goal))"))
        # SOUNDNESS-CRITICAL: reject if fresh variable already occurs in sequent
        !has_clash(sequent, Set([fresh])) ||
            throw(ArgumentError("ForallRightRule: variable $(fresh) is not fresh (occurs in sequent)"))
        new(sequent, target, fresh)
    end
end

# ─────────────────────────────────────────────────────────────────────────────
#                       Left Rules (Hypothesis-Oriented)
# ─────────────────────────────────────────────────────────────────────────────
"""
    ImpliesLeftRule(sequent, target)

→-Left: For hypothesis `A → B`, create subgoals to prove `A` and use `B`.
"""
struct ImpliesLeftRule <: KernelRule
    sequent::Sequent
    target::Ante
    insert::Cons

    function ImpliesLeftRule(sequent::Sequent, target::Ante, insert::Cons)
        1 <= target.idx <= length(sequent.antecedent) || throw(BoundsError(sequent.antecedent, target.idx))
        1 <= insert.idx <= length(sequent.consequent) + 1 || throw(BoundsError(sequent.consequent, insert.idx))
        hyp = sequent.antecedent[target.idx]
        hyp isa Implies || throw(ArgumentError("ImpliesLeftRule requires Implies, got $(typeof(hyp))"))
        new(sequent, target, insert)
    end
end

"""
    NotLeftRule(sequent, target)

¬-Left: For hypothesis `¬A`, move `A` to consequent.
"""
struct NotLeftRule <: KernelRule
    sequent::Sequent
    target::Ante
    insert::Cons

    function NotLeftRule(sequent::Sequent, target::Ante, insert::Cons)
        1 <= target.idx <= length(sequent.antecedent) || throw(BoundsError(sequent.antecedent, target.idx))
        1 <= insert.idx <= length(sequent.consequent) + 1 || throw(BoundsError(sequent.consequent, insert.idx))
        hyp = sequent.antecedent[target.idx]
        hyp isa Not || throw(ArgumentError("NotLeftRule requires Not, got $(typeof(hyp))"))
        new(sequent, target, insert)
    end
end



# ─────────────────────────────────────────────────────────────────────────────
#                            Structural Rules
# ─────────────────────────────────────────────────────────────────────────────

"""
    CloseRule(sequent, ante_ref, cons_ref)

Identity: Close when same formula appears in antecedent and consequent.
"""
struct CloseRule <: KernelRule
    sequent::Sequent
    target_ante::Ante
    target_cons::Cons

    function CloseRule(sequent::Sequent, target_ante::Ante, target_cons::Cons)
        1 <= target_ante.idx <= length(sequent.antecedent) || throw(BoundsError(sequent.antecedent, target_ante.idx))
        1 <= target_cons.idx <= length(sequent.consequent) || throw(BoundsError(sequent.consequent, target_cons.idx))

        hyp = sequent.antecedent[target_ante.idx]
        goal = sequent.consequent[target_cons.idx]
        hyp == goal || throw(ArgumentError("CloseRule: formulas must match"))
        new(sequent, target_ante, target_cons)
    end
end

"""
    SubstitutionRule(sequent, substitution)

Apply substitution to instantiate schematic variables.
"""
struct SubstitutionRule <: KernelRule
    sequent::Sequent
    substitution::Substitution
end

"""
    WeakeningLeftRule(sequent, target)

Remove an unnecessary hypothesis from the antecedent.
In goal-directed proving: to prove Γ, A ⊢ Δ, it suffices to prove Γ ⊢ Δ.
"""
struct WeakeningLeftRule <: KernelRule
    sequent::Sequent
    target::Ante

    function WeakeningLeftRule(sequent::Sequent, target::Ante)
        1 <= target.idx <= length(sequent.antecedent) || throw(BoundsError(sequent.antecedent, target.idx))
        new(sequent, target)
    end
end

"""
    WeakeningRightRule(sequent, target)

Remove an unnecessary goal from the consequent.
In goal-directed proving: to prove Γ ⊢ Δ, A, it suffices to prove Γ ⊢ Δ.
"""
struct WeakeningRightRule <: KernelRule
    sequent::Sequent
    target::Cons

    function WeakeningRightRule(sequent::Sequent, target::Cons)
        1 <= target.idx <= length(sequent.consequent) || throw(BoundsError(sequent.consequent, target.idx))
        new(sequent, target)
    end
end

"""
    CutRule(sequent, cut_formula)

Cut: Introduce a lemma. Creates two subgoals:
1. Prove the cut formula from current hypotheses
2. Use the cut formula to prove the original goal
"""
struct CutRule <: KernelRule
    sequent::Sequent
    cut_formula::Formula
    insert_cons::Cons
    insert_ante::Ante
    function CutRule(sequent::Sequent, cut_formula::Formula, insert_cons::Cons, insert_ante::Ante)
        1 <= insert_cons.idx <= length(sequent.consequent) + 1 || throw(BoundsError(sequent.consequent, insert_cons.idx))
        1 <= insert_ante.idx <= length(sequent.antecedent) + 1 || throw(BoundsError(sequent.antecedent, insert_ante.idx))
        new(sequent, cut_formula, insert_cons, insert_ante)
    end
end

# ─────────────────────────────────────────────────────────────────────────────
#                    GROUND TERM EVALUATION
# ─────────────────────────────────────────────────────────────────────────────

"""
    is_ground_term(t::Term) -> Bool

Check if a term contains no variables.
"""
is_ground_term(::Constant)::Bool = true
is_ground_term(::Variable)::Bool = false
is_ground_term(::Hole)::Bool = false
is_ground_term(t::FunctionApplication) = false
is_ground_term(t::Sum) = is_ground_term(t.left) && is_ground_term(t.right)
is_ground_term(t::Difference)::Bool = is_ground_term(t.left) && is_ground_term(t.right)
is_ground_term(t::Product)::Bool = is_ground_term(t.left) && is_ground_term(t.right)
is_ground_term(t::Division)::Bool = is_ground_term(t.left) && is_ground_term(t.right)
is_ground_term(t::Power)::Bool = is_ground_term(t.base)

"""
    evaluate_ground_term(t::Term) -> Rational

Evaluate a ground term to its numeric value.
Throws an error if the term is not ground.
"""
evaluate_ground_term(c::Constant)::Rational{BigInt} = c.value
evaluate_ground_term(t::Sum)::Rational{BigInt} = evaluate_ground_term(t.left) + evaluate_ground_term(t.right)
evaluate_ground_term(t::Difference)::Rational{BigInt} = evaluate_ground_term(t.left) - evaluate_ground_term(t.right)
evaluate_ground_term(t::Product)::Rational{BigInt} = evaluate_ground_term(t.left) * evaluate_ground_term(t.right)
evaluate_ground_term(t::Division)::Rational{BigInt} = evaluate_ground_term(t.left) / evaluate_ground_term(t.right)
evaluate_ground_term(t::Power)::Rational{BigInt} = evaluate_ground_term(t.base)^t.exponent.value
evaluate_ground_term(::Variable)::Rational{BigInt} = error("Cannot evaluate variable - term is not ground")
evaluate_ground_term(::Hole)::Rational{BigInt} = error("Cannot evaluate hole - term is not ground")
evaluate_ground_term(::FunctionApplication)::Rational{BigInt} = error("Cannot evaluate uninterpreted function application")

# ─────────────────────────────────────────────────────────────────────────────
#                    GROUND INEQUALITY RULE
# ─────────────────────────────────────────────────────────────────────────────

"""
    GroundInequalityRule(left::Term, right::Term)

Prove `⊢ left < right` where both terms are ground and left evaluates to strictly less than right.
This is the kernel's computational rule for arithmetic strict inequality.

Example: `GroundInequalityRule(Constant(1), Constant(3))` proves `⊢ 1 < 3`
"""
struct GroundInequalityRightRule <: KernelRule
    left::Term
    right::Term

    function GroundInequalityRightRule(left::Term, right::Term)
        is_ground_term(left) || throw(ArgumentError("Left term must be ground"))
        is_ground_term(right) || throw(ArgumentError("Right term must be ground"))
        evaluate_ground_term(left) < evaluate_ground_term(right) ||
            throw(ArgumentError("Left term must evaluate to strictly less than right: $(evaluate_ground_term(left)) ≮ $(evaluate_ground_term(right))"))
        new(left, right)
    end
end

"""
    GroundInequalityLeftRule(left::Term, right::Term)

Prove `left < right ⊢ ` where both terms are ground and left evaluates to strictly less than right.
This is the kernel's computational rule for arithmetic strict inequality.

Example: `GroundInequalityLeftRule(Constant(3), Constant(1))` proves `3 < 1 ⊢ `
"""
struct GroundInequalityLeftRule <: KernelRule
    left::Term
    right::Term

    function GroundInequalityLeftRule(left::Term, right::Term)
        is_ground_term(left) || throw(ArgumentError("Left term must be ground"))
        is_ground_term(right) || throw(ArgumentError("Right term must be ground"))
        evaluate_ground_term(left) >= evaluate_ground_term(right) ||
            throw(ArgumentError("Left term must evaluate to strictly less than right: $(evaluate_ground_term(left)) ≮ $(evaluate_ground_term(right))"))
        new(left, right)
    end
end
# ─────────────────────────────────────────────────────────────────────────────
#                         Proof Combination Rules
# ─────────────────────────────────────────────────────────────────────────────

"""
    ApplySubproof(subgoal_idx)

Attach a subproof to an open subgoal of a main derivation.
The main derivation and subproof are the two children of the resulting `Derivation`.
"""
struct ApplySubproof <: KernelRule
    subgoal_idx::Int
end

# ═══════════════════════════════════════════════════════════════════════════════
#                          SECTION 9: DERIVATION
# ═══════════════════════════════════════════════════════════════════════════════

"""
    Derivation

Proof derivation. ONLY constructible through rule constructors.

Fields:
- `assumptions`: open subgoals (sequents still to be proved)
- `conclusion`: the sequent this derivation establishes
- `rule`: the kernel rule applied at this step (`Any`-typed to avoid parametric complexity)
- `children`: tuple of child `Derivation`s fed into this step
"""
struct Derivation
    assumptions::NTuple{N,Sequent} where N
    conclusion::Sequent
    rule::KernelRule
    children::NTuple{M,Derivation} where M
    tools::Set{Symbol}

    # ═══════════════════════════════════════════════════════════════════════════
    #                    RULE-BASED CONSTRUCTORS ONLY
    # ═══════════════════════════════════════════════════════════════════════════

    function Derivation(rule::Assume)
        new(tuple(rule.sequent), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::AxiomRule)
        new(tuple(), Sequent(rule.axiom.formula), rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::UntrustedRule)
        new(tuple(), rule.sequent, rule, tuple(), Set{Symbol}([rule.tool]))
    end

    # --- Right Rules ---

    function Derivation(rule::ImpliesRightRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        goal = cons[rule.target.idx]::Implies

        cons_head = cons[1:rule.target.idx-1]
        cons_tail = cons[rule.target.idx+1:end]
        new_cons = (cons_head..., goal.right, cons_tail...)

        ante_head = ante[1:rule.insert.idx-1]
        ante_tail = ante[rule.insert.idx:end]
        new_ante = (ante_head..., goal.left, ante_tail...)

        new(tuple(Sequent(new_ante, new_cons)), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::NotRightRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        goal = cons[rule.target.idx]::Not

        cons_head = cons[1:rule.target.idx-1]
        cons_tail = cons[rule.target.idx+1:end]
        cons_without_goal = (cons_head..., cons_tail...)

        ante_head = ante[1:rule.insert.idx-1]
        ante_tail = ante[rule.insert.idx:end]
        new_ante = (ante_head..., goal.formula, ante_tail...)

        new(tuple(Sequent(new_ante, cons_without_goal)), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::ForallRightRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        goal = cons[rule.target.idx]::Forall

        ρ = Renaming(goal.variable, rule.fresh)
        new_body = rename(goal.body, ρ)

        # Replace at the same position
        cons_head = cons[1:rule.target.idx-1]
        cons_tail = cons[rule.target.idx+1:end]
        new_cons = (cons_head..., new_body, cons_tail...)

        new(tuple(Sequent(ante, new_cons)), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    # --- Left Rules ---

    function Derivation(rule::ImpliesLeftRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        hyp = ante[rule.target.idx]::Implies

        ante_head = ante[1:rule.target.idx-1]
        ante_tail = ante[rule.target.idx+1:end]
        ante_without_hyp = (ante_head..., ante_tail...)

        cons_head = cons[1:rule.insert.idx-1]
        cons_tail = cons[rule.insert.idx:end]

        show_seq = Sequent(ante_without_hyp, (cons_head..., hyp.left, cons_tail...))
        use_seq = Sequent((ante_head..., hyp.right, ante_tail...), cons)

        new(tuple(show_seq, use_seq), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::NotLeftRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        hyp = ante[rule.target.idx]::Not

        ante_head = ante[1:rule.target.idx-1]
        ante_tail = ante[rule.target.idx+1:end]
        ante_without_hyp = (ante_head..., ante_tail...)

        cons_head = cons[1:rule.insert.idx-1]
        cons_tail = cons[rule.insert.idx:end]
        new_cons = (cons_head..., hyp.formula, cons_tail...)

        new(tuple(Sequent(ante_without_hyp, new_cons)), rule.sequent, rule, tuple(), Set{Symbol}())
    end


    # --- Structural Rules ---

    function Derivation(rule::CloseRule)
        new(tuple(), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::SubstitutionRule)
        subst_ante = Tuple(substitute(f, rule.substitution) for f in rule.sequent.antecedent)
        subst_cons = Tuple(substitute(f, rule.substitution) for f in rule.sequent.consequent)
        new(tuple(rule.sequent), Sequent(subst_ante, subst_cons), rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::WeakeningLeftRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        # Remove the formula at target.idx from antecedent
        hyp = ante[rule.target.idx]
        ante_head = ante[1:rule.target.idx-1]
        ante_tail = ante[rule.target.idx+1:end]
        ante_without_hyp = (ante_head..., ante_tail...)

        new(tuple(Sequent(ante_without_hyp, cons)), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::WeakeningRightRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        # Remove the formula at target.idx from consequent
        goal = cons[rule.target.idx]
        cons_head = cons[1:rule.target.idx-1]
        cons_tail = cons[rule.target.idx+1:end]
        cons_without_goal = (cons_head..., cons_tail...)

        new(tuple(Sequent(ante, cons_without_goal)), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::CutRule)
        ante = rule.sequent.antecedent
        cons = rule.sequent.consequent

        # Subgoal 1: Γ1, Γ2 ⊢ Δ1, A, Δ2  (prove the cut formula)
        cons_head = cons[1:rule.insert_cons.idx-1]
        cons_tail = cons[rule.insert_cons.idx:end]
        show_cons = (cons_head..., rule.cut_formula, cons_tail...)
        show_seq = Sequent(ante, show_cons)

        # Subgoal 2: Γ1, A, Γ2 ⊢ Δ1, Δ2 (use the cut formula)
        ante_head = ante[1:rule.insert_ante.idx-1]
        ante_tail = ante[rule.insert_ante.idx:end]
        use_ante = (ante_head..., rule.cut_formula, ante_tail...)
        use_seq = Sequent(use_ante, cons)

        new(tuple(show_seq, use_seq), rule.sequent, rule, tuple(), Set{Symbol}())
    end

    # --- Ground Inequality and Positive Constant Rules ---

    function Derivation(rule::GroundInequalityRightRule)
        # Complete proof: ⊢ left < right with no premises
        # The inequality is true because left evaluates to strictly less than right
        conclusion = Sequent(LessThan(rule.left, rule.right))
        new(tuple(), conclusion, rule, tuple(), Set{Symbol}())
    end

    function Derivation(rule::GroundInequalityLeftRule)
        # Complete proof: ⊢ left < right with no premises
        # The inequality is true because left evaluates to strictly less than right
        conclusion = Sequent(tuple(LessThan(rule.left, rule.right)), tuple())
        new(tuple(), conclusion, rule, tuple(), Set{Symbol}())
    end

    # --- Proof Combination (ApplySubproofRule defined below) ---

    function Derivation(main::Derivation, subgoal_idx::Int, sub::Derivation)
        assumps = main.assumptions

        1 <= subgoal_idx <= length(assumps) || throw(BoundsError(assumps, subgoal_idx))

        target = assumps[subgoal_idx]
        target == sub.conclusion ||
            throw(ArgumentError("Subproof conclusion doesn't match target: expected $(target), got $(sub.conclusion)"))

        # Split the assumptions around the target subgoal
        assump_head = assumps[1:subgoal_idx-1]
        assump_tail = assumps[subgoal_idx+1:end]

        # Splat the subproof's open assumptions into the hole left by the target
        new_assumptions = (assump_head..., sub.assumptions..., assump_tail...)

        rule = ApplySubproof(subgoal_idx)

        new(new_assumptions, main.conclusion, rule, (main, sub), union(main.tools, sub.tools))
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#                              EXPORTS
# ═══════════════════════════════════════════════════════════════════════════════

# Core types
export Term, Variable, Constant, FunctionSymbol, FunctionApplication
export Sum, Difference, Product, Division, Power, Hole
export Formula, PredicateSymbol, PredicateApplication
export LessThan, Equals
export Not, Implies, Forall
export ZERO, ONE
export _x_sym, _y_sym, _z_sym, _w_sym, _a_sym, _b_sym, _c_sym
export _x, _y, _z, _w, _a, _b, _c
export _P_sym, _Q_sym, _C_sym, _C

# Proof machinery
export Sequent, Derivation, KernelAxiom
export Ante, Cons, SequentPosition
export Substitution, substitute

# Kernel rules
export Assume, AxiomRule, UntrustedRule
export ImpliesRightRule, NotRightRule, ForallRightRule
export ImpliesLeftRule, NotLeftRule
export CloseRule, SubstitutionRule
export WeakeningLeftRule, WeakeningRightRule
export CutRule
export GroundInequalityRightRule, GroundInequalityLeftRule
export ApplySubproof
export is_ground_term, evaluate_ground_term

# Kernel axioms
export AX_EQ_REFL
export AX_CONG_PRED, AX_CONG_CONTEXT
export AX_ADD_ID, AX_ADD_INV
export AX_ADD_COMM, AX_ADD_ASSO
export AX_MUL_ID, AX_MUL_INV
export AX_MUL_COMM, AX_MUL_ASSO
export AX_DIS
export AX_DIFF
export AX_LT_IRREFLEXIVITY, AX_LT_TRANS, AX_LT_TRICHOTOMY
export AX_LT_ADD, AX_LT_MUL_POS
export AX_LEQ_SUB, AX_LEQ_ADD, AX_LEQ_SCALE_LEFT, AX_LEQ_SCALE_RIGHT
export AX_LEQ_SCALE_LEFT_NEG, AX_LEQ_SCALE_RIGHT_NEG
export AX_LEQ_TRANS, AX_LEQ_SUB_TO_ZERO, AX_LT_SUB_TO_ZERO
export AX_FORALL_INST
export KERNEL_FIELD_AXIOMS, KERNEL_ORDER_AXIOMS

end # module Kernel
