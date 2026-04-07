# ═══════════════════════════════════════════════════════════════════════════════
#                    ELENCHOS SYNTAX LAYER (MINIMAL KERNEL)
#                         Syntax sugar, display, utilities
# ═══════════════════════════════════════════════════════════════════════════════
#
# This module is NOT soundness-critical.
#
# The kernel uses minimal primitives:
#   - Connectives: {¬, →, ∀}
#   - Comparison:  {<}
#
# This layer provides:
#   - Operator overloading for natural syntax
#   - Pretty printing that recognizes defined connectives
#   - Arithmetic terms
#
# ═══════════════════════════════════════════════════════════════════════════════

module Syntax

using ..Kernel

# Re-export kernel types
export Term, Variable, Constant, FunctionSymbol, FunctionApplication
export Sum, Difference, Product, Division, Power  # Arithmetic terms (from kernel)
export Formula, PredicateSymbol, PredicateApplication
export LessThan  # Primitive comparison (from kernel)
export LessOrEqual, Equals, GreaterOrEqual, GreaterThan  # Defined comparisons (from kernel)
export Not, Implies, Forall  # Primitive connectives
export And, Or, Exists, Iff  # Defined connectives
export Sequent, Derivation, KernelAxiom
export Ante, Cons
export Substitution, substitute
export ∧, ∨, →, ¬, ∀, ∃, ↔
# Kernel rules - Logical
export Assume, AxiomRule
export ImpliesRightRule, NotRightRule, ForallRightRule
export ImpliesLeftRule, NotLeftRule

# Kernel rules - Structural
export CloseRule, SubstitutionRule
export WeakeningLeftRule, WeakeningRightRule
export CutRule
export _x_sym, _y_sym, _z_sym, _w_sym, _x, _y, _z, _w
export _a_sym, _b_sym, _c_sym, _a, _b, _c
export _P_sym, _Q_sym, _C_sym, _C
export ZERO, ONE

export is_and_pattern, is_or_pattern, is_exists_pattern, is_equals_pattern, is_lessorequal_pattern
export print_proof_tree, rule_name

# ═══════════════════════════════════════════════════════════════════════════════
#                    CALLABLE SYNTAX (CONVENIENCE, NOT SOUNDNESS-CRITICAL)
# ═══════════════════════════════════════════════════════════════════════════════

(σ::Substitution)(expr) = substitute(expr, σ)

# ═══════════════════════════════════════════════════════════════════════════════
#              DEFINED CONNECTIVES AND COMPARISONS
#              Pure sugar over the primitive basis {¬, →, ∀, <}
# ═══════════════════════════════════════════════════════════════════════════════

And(left::Formula, right::Formula) = Not(Implies(left, Not(right)))
Or(left::Formula, right::Formula) = Implies(Not(left), right)
Exists(variable::Variable, body::Formula) = Not(Forall(variable, Not(body)))
Iff(left::Formula, right::Formula) = And(Implies(left, right), Implies(right, left))
LessOrEqual(left::Term, right::Term) = Not(LessThan(right, left))
GreaterOrEqual(left::Term, right::Term) = LessOrEqual(right, left)
GreaterThan(left::Term, right::Term) = LessThan(right, left)

# ═══════════════════════════════════════════════════════════════════════════════
#                         OPERATOR OVERLOADING
# ═══════════════════════════════════════════════════════════════════════════════

# --- Term Operators ---

Base.:+(a::Term, b::Term) = Sum(a, b)
Base.:+(a::Term, b::Number) = Sum(a, Constant(b))
Base.:+(a::Number, b::Term) = Sum(Constant(a), b)

Base.:-(a::Term, b::Term) = Difference(a, b)
Base.:-(a::Term, b::Number) = Difference(a, Constant(b))
Base.:-(a::Number, b::Term) = Difference(Constant(a), b)

Base.:*(a::Term, b::Term) = Product(a, b)
Base.:*(a::Term, b::Number) = Product(a, Constant(b))
Base.:*(a::Number, b::Term) = Product(Constant(a), b)

Base.:/(a::Term, b::Term) = Division(a, b)
Base.:/(a::Term, b::Number) = Division(a, Constant(b))
Base.:/(a::Number, b::Term) = Division(Constant(a), b)

function Base.:^(a::Term, b::Integer)
    b >= 0 || error("Exponent must be non-negative")
    Power(a, Constant(b))
end

# --- Formula Operators ---

Base.:~(a::Term, b::Term) = Equals(a, b)
Base.:~(a::Term, b::Number) = Equals(a, Constant(b))
Base.:~(a::Number, b::Term) = Equals(Constant(a), b)
Base.:~(a::Number, b::Number) = Equals(Constant(a), Constant(b))

Base.:(<)(a::Term, b::Term) = LessThan(a, b)
Base.:(<)(a::Term, b::Number) = LessThan(a, Constant(b))
Base.:(<)(a::Number, b::Term) = LessThan(Constant(a), b)

Base.:(>)(a::Term, b::Term) = GreaterThan(a, b)
Base.:(>)(a::Term, b::Number) = GreaterThan(a, Constant(b))
Base.:(>)(a::Number, b::Term) = GreaterThan(Constant(a), b)

# ≤ uses the defined LessOrEqual (which is ¬(b < a))
Base.:(≤)(a::Term, b::Term) = LessOrEqual(a, b)
Base.:(≤)(a::Term, b::Number) = LessOrEqual(a, Constant(b))
Base.:(≤)(a::Number, b::Term) = LessOrEqual(Constant(a), b)

# ≥ is the flip of ≤
Base.:(≥)(a::Term, b::Term) = GreaterOrEqual(a, b)
Base.:(≥)(a::Term, b::Number) = GreaterOrEqual(a, Constant(b))
Base.:(≥)(a::Number, b::Term) = GreaterOrEqual(Constant(a), b)

# Shorthand for Constant - useful when standalone numbers are needed
const c = Constant

export c

# Logical operators (using kernel's defined connectives)
(∧)(a::Formula, b::Formula) = And(a, b)
(∨)(a::Formula, b::Formula) = Or(a, b)
(→)(a::Formula, b::Formula) = Implies(a, b)
(¬)(a::Formula) = Not(a)
(∀)(v::Variable, body::Formula) = Forall(v, body)
(∃)(v::Variable, body::Formula) = Exists(v, body)
(↔)(a::Formula, b::Formula) = Iff(a, b)


Base.:(&)(a::Formula, b::Formula) = And(a, b)
Base.:(|)(a::Formula, b::Formula) = Or(a, b)
function ⊢(fml::Formula)
    Sequent((), (fml,))
end

function ⊢(ante::Tuple, cons::Tuple)
    Sequent(ante, cons)
end

function ⊢(ante::Formula, cons::Formula)
    Sequent((ante,), (cons,))
end

function ⊢(ante::Tuple, cons::Formula)
    Sequent(ante, (cons,))
end

export ∧, ∨, →, ¬, ∀, ∃, ↔, ⊢
# ═══════════════════════════════════════════════════════════════════════════════
#                            PATTERN RECOGNITION
#         Recognize defined connectives in their primitive encoding
# ═══════════════════════════════════════════════════════════════════════════════

"""Check if formula matches pattern for And: ¬(A → ¬B)"""
function is_and_pattern(f::Formula)
    f isa Not || return nothing
    inner = f.formula
    inner isa Implies || return nothing
    inner.right isa Not || return nothing
    return (inner.left, inner.right.formula)  # Returns (A, B) or nothing
end

"""Check if formula matches pattern for Or: ¬A → B"""
function is_or_pattern(f::Formula)
    f isa Implies || return nothing
    f.left isa Not || return nothing
    return (f.left.formula, f.right)  # Returns (A, B) or nothing
end

"""Check if formula matches pattern for Exists: ¬∀x.¬P"""
function is_exists_pattern(f::Formula)
    f isa Not || return nothing
    inner = f.formula
    inner isa Forall || return nothing
    inner.body isa Not || return nothing
    return (inner.variable, inner.body.formula)  # Returns (x, P) or nothing
end

"""Check if formula matches pattern for Equals: now a primitive type"""
function is_equals_pattern(f::Formula)
    f isa Equals || return nothing
    return (f.left, f.right)
end

"""Check if formula matches pattern for LessThan: directly a LessThan"""
function is_lessthan_pattern(f::Formula)
    f isa LessThan || return nothing
    return (f.left, f.right)
end

"""Check if formula matches pattern for LessOrEqual: ¬(b < a)"""
function is_lessorequal_pattern(f::Formula)
    f isa Not || return nothing
    f.formula isa LessThan || return nothing
    return (f.formula.right, f.formula.left)  # a ≤ b = ¬(b < a) → (a, b)
end

# ═══════════════════════════════════════════════════════════════════════════════
#                            PRETTY PRINTING
# ═══════════════════════════════════════════════════════════════════════════════

# --- Terms ---

function Base.show(io::IO, v::Variable)
    print(io, v.name)
end
function Base.show(io::IO, c::Constant)
    isone(denominator(c.value)) ? print(io, numerator(c.value)) : print(io, c.value)
end

Base.show(io::IO, fs::FunctionSymbol) = print(io, fs.name)

function Base.show(io::IO, app::FunctionApplication)
    isempty(app.arguments) ? print(io, "$(app.symbol.name)()") :
    print(io, "$(app.symbol.name)($(join(app.arguments, ", ")))")
end

Base.show(io::IO, t::Sum) = print(io, "($(t.left) + $(t.right))")

function Base.show(io::IO, t::Difference)
    right_str = t.right isa Sum ? "($(t.right))" : "$(t.right)"
    print(io, "$(t.left) - $right_str")
end

function Base.show(io::IO, t::Product)
    left_str = (t.left isa Sum || t.left isa Difference) ? "($(t.left))" : "$(t.left)"
    right_str = (t.right isa Sum || t.right isa Difference) ? "($(t.right))" : "$(t.right)"
    print(io, "$left_str * $right_str")
end

function Base.show(io::IO, t::Division)
    left_str = (t.left isa Sum || t.left isa Difference) ? "($(t.left))" : "$(t.left)"
    right_str = (t.right isa Sum || t.right isa Difference || t.right isa Product || t.right isa Division) ? "($(t.right))" : "$(t.right)"
    print(io, "$left_str / $right_str")
end

function Base.show(io::IO, t::Power)
    base_str = (t.base isa Sum || t.base isa Difference || t.base isa Product || t.base isa Division) ? "($(t.base))" : "$(t.base)"
    print(io, "$base_str^$(t.exponent)")
end

# --- Formulas (with pattern recognition for defined connectives) ---

Base.show(io::IO, ps::PredicateSymbol) = print(io, ps.name)

function Base.show(io::IO, app::PredicateApplication)
    if isempty(app.arguments)
        print(io, "$(app.symbol.name)()")
    else
        print(io, "$(app.symbol.name)($(join(app.arguments, ", ")))")
    end
end

# Primitive comparison
Base.show(io::IO, f::LessThan) = print(io, "$(f.left) < $(f.right)")

# Primitive equality
Base.show(io::IO, f::Equals) = print(io, "$(f.left) ~ $(f.right)")

function Base.show(io::IO, f::Not)
    # Check for LessOrEqual: ¬(b < a) = a ≤ b
    le_parts = is_lessorequal_pattern(f)
    if le_parts !== nothing
        a, b = le_parts
        print(io, "$(a) ≤ $(b)")
        return
    end

    # Check if it's And or Exists (general case)
    and_parts = is_and_pattern(f)
    if and_parts !== nothing
        A, B = and_parts
        print(io, "$(A) ∧ $(B)")
        return
    end

    exists_parts = is_exists_pattern(f)
    if exists_parts !== nothing
        x, P = exists_parts
        print(io, "∃($x, $(P))")
        return
    end

    print(io, "¬($(f.formula))")
end

function Base.show(io::IO, f::Implies)
    # Check if it's really Or
    or_parts = is_or_pattern(f)
    if or_parts !== nothing
        A, B = or_parts
        print(io, "($(A) ∨ $(B))")
        return
    end

    print(io, "($(f.left) → $(f.right))")
end

function Base.show(io::IO, f::Forall)
    print(io, "∀($(f.variable), $(f.body))")
end

# --- Proof State ---

function Base.show(io::IO, s::Sequent)
    blue = get(io, :color, false) ? "\x1b[34m" : ""
    reset = get(io, :color, false) ? "\x1b[0m" : ""

    ante = join(s.antecedent, ", ")
    ante_str = ante == "" ? "" : "($ante)"
    cons = join(s.consequent, ", ")
    cons_str = cons == "" ? "" : "($cons)"

    if isempty(s.antecedent)
        print(io, blue, "⊢ ", reset, cons_str)
    else
        print(io, ante_str, blue, " ⊢ ", reset, cons_str)
    end
end

function Base.show(io::IO, proof::Derivation)
    if isempty(proof.assumptions)
        if isempty(proof.tools)
            print(io, "No goals: $(proof.conclusion)")
        else
            print(io, "No goals: $(proof.conclusion) [$(join(proof.tools, ", "))]")
        end
        return
    end

    for (i, assumption) in enumerate(proof.assumptions)
        length(proof.assumptions) > 1 && println(io, "Goal $i:")
        show(io, assumption)
        i < length(proof.assumptions) && println(io)
    end
end

Base.show(io::IO, axiom::KernelAxiom) = print(io, "Axiom: $(axiom.formula)")

function Base.show(io::IO, σ::Kernel.SymbolSubstitution)
    func_pairs = ["$k ↦ $v" for (k, v) in σ.bindings]
    pred_pairs = ["$k ↦ $v" for (k, v) in σ.pred_bindings]
    all_pairs = vcat(func_pairs, pred_pairs)
    print(io, "σ{$(join(all_pairs, ", "))}")
end

function Base.show(io::IO, σ::Kernel.HoleSubstitution)
    hole_pairs = ["$(k) ↦ $(v)" for (k, v) in σ.hole_bindings]
    print(io, "σ{$(join(hole_pairs, ", "))}")
end

# ═══════════════════════════════════════════════════════════════════════════════
#                           PROOF TREE DISPLAY
# ═══════════════════════════════════════════════════════════════════════════════

"""
    rule_name(r) -> String

Short human-readable name for a kernel rule or proof combination step.
"""
rule_name(::Assume) = "Assume"
rule_name(::AxiomRule) = "Ax"
rule_name(::ImpliesRightRule) = "→R"
rule_name(::ImpliesLeftRule) = "→L"
rule_name(::NotRightRule) = "¬R"
rule_name(::NotLeftRule) = "¬L"
rule_name(::ForallRightRule) = "∀R"
rule_name(::CloseRule) = "Close"
rule_name(::SubstitutionRule) = "Subst"
rule_name(::WeakeningLeftRule) = "WL"
rule_name(::WeakeningRightRule) = "WR"
rule_name(::CutRule) = "Cut"
rule_name(::GroundInequalityRightRule) = "ArithR"
rule_name(::GroundInequalityLeftRule) = "ArithL"
rule_name(r::ApplySubproof) = "Apply[$(r.subgoal_idx)]"
rule_name(r) = string(typeof(r))

# ── Logical tree extraction (flatten Apply nodes) ────────────────────────────

"""Internal node for the logical proof tree."""
mutable struct _INode
    name::String
    conclusion::String
    premises::Vector{_INode}
    is_open::Bool
end

_plain_sequent(s::Sequent) = sprint(show, s, context=:color => false)

"""Extract logical inference tree from a Derivation, flattening Apply nodes."""
function _to_inference_tree(d::Derivation)::_INode
    if d.rule isa Assume
        return _INode("?", _plain_sequent(d.conclusion), _INode[], true)
    elseif d.rule isa ApplySubproof
        main_tree = _to_inference_tree(d.children[1])
        sub_tree = _to_inference_tree(d.children[2])
        return _fill_nth_open(main_tree, d.rule.subgoal_idx, sub_tree)
    else
        prems = [_INode("?", _plain_sequent(s), _INode[], true) for s in d.assumptions]
        return _INode(rule_name(d.rule), _plain_sequent(d.conclusion), prems, false)
    end
end

function _fill_nth_open(tree::_INode, n::Int, replacement::_INode)::_INode
    _, result = _fill_impl(tree, n, replacement, Ref(0))
    result
end

function _fill_impl(tree::_INode, n::Int, replacement::_INode, count::Ref{Int})
    if tree.is_open
        count[] += 1
        return count[] == n ? (true, replacement) : (false, tree)
    end
    new_prems = _INode[]
    done = false
    for p in tree.premises
        if done
            push!(new_prems, p)
        else
            (done, new_p) = _fill_impl(p, n, replacement, count)
            push!(new_prems, new_p)
        end
    end
    (done, _INode(tree.name, tree.conclusion, new_prems, false))
end

# ── Inference-style rendering ────────────────────────────────────────────────

struct _Rendered
    lines::Vector{String}
    width::Int
end

function _pad_right(s::String, w::Int)
    tw = textwidth(s)
    tw >= w ? s : s * " "^(w - tw)
end

function _center(s::String, w::Int)
    tw = textwidth(s)
    tw >= w && return s
    left = (w - tw) ÷ 2
    " "^left * s * " "^(w - tw - left)
end

function _render_inference(node::_INode)::_Rendered
    concl = node.conclusion
    name = node.name
    concl_w = textwidth(concl)

    # Open (unproved) subgoal
    if node.is_open
        label = concl * " (?)"
        w = textwidth(label)
        return _Rendered([label], w)
    end

    # Leaf rule (no premises above the line)
    if isempty(node.premises)
        bar_w = max(concl_w + 2, 6)
        bar = "─"^bar_w * " " * name
        total_w = textwidth(bar)

        # Center conclusion under the bar part (bar_w)
        # but the whole line must have total_w
        c_line = _pad_right(_center(concl, bar_w), total_w)
        return _Rendered([bar, c_line], total_w)
    end

    # Render premises and place them side-by-side
    rps = [_render_inference(p) for p in node.premises]
    combined = _combine_horiz(rps)
    prem_w = combined.width

    # Bar spans at least the premises and the conclusion
    bar_w = max(prem_w, concl_w + 2)
    bar = "─"^bar_w * " " * name
    total_w = textwidth(bar)

    lines = String[]
    # Center premises block over the bar part (bar_w)
    offset = max(0, (bar_w - prem_w) ÷ 2)
    for line in combined.lines
        push!(lines, _pad_right(" "^offset * line, total_w))
    end

    # The bar line already has total_w
    push!(lines, bar)

    # Center conclusion under the bar part (bar_w)
    push!(lines, _pad_right(_center(concl, bar_w), total_w))

    _Rendered(lines, total_w)
end

function _combine_horiz(rendered::Vector{_Rendered})::_Rendered
    length(rendered) == 1 && return rendered[1]
    gap = 2
    max_h = maximum(length(r.lines) for r in rendered)
    lines = String[]
    for row in 1:max_h
        parts = String[]
        for r in rendered
            deficit = max_h - length(r.lines)
            if row <= deficit
                push!(parts, " "^r.width)
            else
                push!(parts, _pad_right(r.lines[row-deficit], r.width))
            end
        end
        push!(lines, join(parts, " "^gap))
    end
    total_w = sum(r.width for r in rendered) + gap * (length(rendered) - 1)
    _Rendered(lines, total_w)
end

# ── Public API ───────────────────────────────────────────────────────────────

"""
    print_proof_tree([io], derivation)

Print the proof as an inference tree in the style of logic papers.
Apply (proof combination) nodes are flattened — only logical
rule applications are shown.  Premises appear above the inference
line, the conclusion below it.
"""
print_proof_tree(d::Derivation) = print_proof_tree(stdout, d)

function print_proof_tree(io::IO, d::Derivation)
    tree = _to_inference_tree(d)
    rendered = _render_inference(tree)
    for line in rendered.lines
        println(io, line)
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
# ═══════════════════════════════════════════════════════════════════════════════
#                              MACROS
# ═══════════════════════════════════════════════════════════════════════════════

macro vars(names...)
    exprs = [:($(esc(name)) = Variable($(string(name)))) for name in names]
    Expr(:block, exprs...)
end

macro funcs(names...)
    exprs = [:($(esc(name)) = FunctionSymbol($(string(name)))) for name in names]
    Expr(:block, exprs...)
end

macro preds(names...)
    exprs = [:($(esc(name)) = PredicateSymbol($(string(name)))) for name in names]
    Expr(:block, exprs...)
end

export @vars, @funcs, @preds

# ═══════════════════════════════════════════════════════════════════════════════
#                    SCHEMATIC UNIFICATION (imported from Unification module)
# ═══════════════════════════════════════════════════════════════════════════════

# Note: unify, is_schematic, is_ground, match_subterm are now 
# defined in Unification module (src/unification.jl). They are re-exported here 
# for backwards compatibility. unify now returns Union{Substitution, Nothing}.

using ..Unification: unify, is_schematic, is_ground, match_subterm

export unify, is_schematic, is_ground, match_subterm

end # module Syntax
