module Serialization

using ..Kernel

export serialize_proof, deserialize_proof

# ═══════════════════════════════════════════════════════════════════════════════
#                    PROOF SERIALIZATION (S-expression certificates)
# ═══════════════════════════════════════════════════════════════════════════════

# ── S-expression representation for terms ────────────────────────────────────

_sexp(t::Variable) = t.name
function _sexp(c::Constant)
    isone(denominator(c.value)) ? string(numerator(c.value)) :
    string(numerator(c.value), "/", denominator(c.value))
end
function _sexp(t::FunctionApplication)
    isempty(t.arguments) ? "$(t.symbol.name)()" :
    "($(t.symbol.name) $(join((_sexp(a) for a in t.arguments), " ")))"
end
_sexp(t::Sum) = "(+ $(_sexp(t.left)) $(_sexp(t.right)))"
_sexp(t::Difference) = "(- $(_sexp(t.left)) $(_sexp(t.right)))"
_sexp(t::Product) = "(* $(_sexp(t.left)) $(_sexp(t.right)))"
_sexp(t::Division) = "(/ $(_sexp(t.left)) $(_sexp(t.right)))"
_sexp(t::Power) = "(^ $(_sexp(t.base)) $(_sexp(t.exponent)))"
_sexp(t::Hole) = "(hole $(t.index))"

# ── S-expression representation for formulas ─────────────────────────────────

function _sexp(f::PredicateApplication)
    isempty(f.arguments) ? "$(f.symbol.name)()" :
    "($(f.symbol.name) $(join((_sexp(a) for a in f.arguments), " ")))"
end
_sexp(f::LessThan) = "(Lt $(_sexp(f.left)) $(_sexp(f.right)))"
_sexp(f::Equals) = "(Eq $(_sexp(f.left)) $(_sexp(f.right)))"
_sexp(f::Not) = "(Not $(_sexp(f.formula)))"
_sexp(f::Implies) = "(Imp $(_sexp(f.left)) $(_sexp(f.right)))"
_sexp(f::Forall) = "(All $(f.variable.name) $(_sexp(f.body)))"

# ── S-expression for substitution ────────────────────────────────────────────

function _sexp(σ::Substitution)
    parts = String[]
    for (k, v) in σ.bindings
        push!(parts, "(fn $(k.name) $(_sexp(v)))")
    end
    for (k, v) in σ.pred_bindings
        push!(parts, "(pred $(k.name) $(_sexp(v)))")
    end
    "($(join(parts, " ")))"
end

# ── Flattened certificate tree (collapses ApplySubproof nodes) ───────────────

mutable struct _CertNode
    rule::Any             # nothing for open goals
    conclusion::Sequent
    children::Vector{_CertNode}
    is_open::Bool
end

"""Extract flattened proof certificate from a Derivation, removing Apply nodes."""
function _to_cert_tree(d::Derivation)::_CertNode
    if d.rule isa Assume
        return _CertNode(nothing, d.conclusion, _CertNode[], true)
    elseif d.rule isa ApplySubproof
        main = _to_cert_tree(d.children[1])
        sub = _to_cert_tree(d.children[2])
        return _fill_cert_open(main, d.rule.subgoal_idx, sub)
    else
        prems = [_CertNode(nothing, s, _CertNode[], true) for s in d.assumptions]
        return _CertNode(d.rule, d.conclusion, prems, false)
    end
end

function _fill_cert_open(tree::_CertNode, n::Int, replacement::_CertNode)::_CertNode
    _, result = _fill_cert_impl(tree, n, replacement, Ref(0))
    result
end

function _fill_cert_impl(tree::_CertNode, n::Int, replacement::_CertNode, count::Ref{Int})
    if tree.is_open
        count[] += 1
        return count[] == n ? (true, replacement) : (false, tree)
    end
    new_children = _CertNode[]
    done = false
    for c in tree.children
        if done
            push!(new_children, c)
        else
            (done, new_c) = _fill_cert_impl(c, n, replacement, count)
            push!(new_children, new_c)
        end
    end
    (done, _CertNode(tree.rule, tree.conclusion, new_children, false))
end

# ── Rule S-expression tags and arguments ─────────────────────────────────────

_rule_tag(::ImpliesRightRule) = "ImpR"
_rule_tag(::NotRightRule) = "NotR"
_rule_tag(::ForallRightRule) = "AllR"
_rule_tag(::ImpliesLeftRule) = "ImpL"
_rule_tag(::NotLeftRule) = "NotL"
_rule_tag(::CloseRule) = "Close"
_rule_tag(::AxiomRule) = "Axiom"
_rule_tag(::SubstitutionRule) = "Subst"
_rule_tag(::WeakeningLeftRule) = "WL"
_rule_tag(::WeakeningRightRule) = "WR"
_rule_tag(::CutRule) = "Cut"
_rule_tag(::GroundInequalityRightRule) = "ArithR"
_rule_tag(::GroundInequalityLeftRule) = "ArithL"

_rule_args(r::ImpliesRightRule) = " $(r.target.idx) $(r.insert.idx)"
_rule_args(r::NotRightRule) = " $(r.target.idx) $(r.insert.idx)"
_rule_args(r::ForallRightRule) = " $(r.target.idx) $(r.fresh.name)"
_rule_args(r::ImpliesLeftRule) = " $(r.target.idx) $(r.insert.idx)"
_rule_args(r::NotLeftRule) = " $(r.target.idx) $(r.insert.idx)"

_rule_args(r::CloseRule) = " $(r.target_ante.idx) $(r.target_cons.idx)"
_rule_args(r::AxiomRule) = " $(_sexp(r.axiom.formula))"
function _rule_args(r::SubstitutionRule)
    ante = join((_sexp(f) for f in r.sequent.antecedent), " ")
    cons = join((_sexp(f) for f in r.sequent.consequent), " ")
    " (($ante) ($cons)) $(_sexp(r.substitution))"
end
_rule_args(r::WeakeningLeftRule) = " $(r.target.idx)"
_rule_args(r::WeakeningRightRule) = " $(r.target.idx)"
_rule_args(r::CutRule) = " $(_sexp(r.cut_formula)) $(r.insert_cons.idx) $(r.insert_ante.idx)"
_rule_args(r::GroundInequalityRightRule) = " $(_sexp(r.left)) $(_sexp(r.right))"
_rule_args(r::GroundInequalityLeftRule) = " $(_sexp(r.left)) $(_sexp(r.right))"

# ── Serialization output ────────────────────────────────────────────────────

function _serialize_node(io::IO, node::_CertNode, indent::Int)
    pad = "  "^indent

    if node.is_open
        println(io, pad, "(Open)")
        return
    end

    tag = _rule_tag(node.rule)
    args = _rule_args(node.rule)

    if isempty(node.children)
        println(io, pad, "(", tag, args, ")")
    else
        println(io, pad, "(", tag, args)
        for child in node.children
            _serialize_node(io, child, indent + 1)
        end
        println(io, pad, ")")
    end
end

"""
    serialize_proof(derivation) -> String

Serialize a proof derivation as a compact S-expression certificate.

The certificate contains only the goal formula and the tree of rule
applications with their arguments (indices, terms, substitutions).
No sequents are stored — a checker recomputes them from the rules.

Apply (proof combination) nodes are flattened away; the certificate
shows only logical rule applications in a tree whose branching
mirrors the inference structure.
"""
function serialize_proof(d::Derivation)::String
    io = IOBuffer()
    cert = _to_cert_tree(d)
    ante = join((_sexp(f) for f in d.conclusion.antecedent), " ")
    cons = join((_sexp(f) for f in d.conclusion.consequent), " ")
    println(io, "(proof (($ante) ($cons))")
    _serialize_node(io, cert, 1)
    println(io, ")")
    String(take!(io))
end

# ═══════════════════════════════════════════════════════════════════════════════
#                    PROOF DESERIALIZATION (replay from certificate)
# ═══════════════════════════════════════════════════════════════════════════════

# ── S-expression parser ──────────────────────────────────────────────────────

const _SExp = Union{String,Vector{Any}}

function _tokenize(s::String)::Vector{String}
    tokens = String[]
    n = ncodeunits(s)
    i = 1
    while i <= n
        c = s[i]
        if c == '(' || c == ')'
            push!(tokens, string(c))
            i += 1
        elseif c in (' ', '\n', '\t', '\r')
            i += 1
        else
            j = i + 1
            while j <= n && s[j] ∉ ('(', ')', ' ', '\n', '\t', '\r')
                j += 1
            end
            tok = s[i:j-1]
            # Absorb trailing "()" for nullary applications like _P()
            if j + 1 <= n && s[j] == '(' && s[j+1] == ')'
                tok *= "()"
                j += 2
            end
            push!(tokens, tok)
            i = j
        end
    end
    tokens
end

function _parse_sexp(tokens::Vector{String}, pos::Int)::Tuple{_SExp,Int}
    if tokens[pos] == "("
        elems = Any[]
        pos += 1
        while tokens[pos] != ")"
            elem, pos = _parse_sexp(tokens, pos)
            push!(elems, elem)
        end
        return elems, pos + 1
    else
        return tokens[pos], pos + 1
    end
end

function _parse_sexp(s::String)::_SExp
    tokens = _tokenize(s)
    result, _ = _parse_sexp(tokens, 1)
    result
end

# ── Term reconstruction ──────────────────────────────────────────────────────

function _recon_term(sexp::String)::Term
    # Nullary function application: name()
    if endswith(sexp, "()")
        return FunctionApplication(FunctionSymbol(sexp[1:end-2]), ())
    end
    # Integer constant
    v = tryparse(Int, sexp)
    v !== nothing && return Constant(v)
    # Rational constant
    if '/' in sexp
        parts = split(sexp, '/')
        return Constant(parse(Int, parts[1]) // parse(Int, parts[2]))
    end
    # Variable
    Variable(sexp)
end

function _recon_term(sexp::Vector)::Term
    head = sexp[1]::String
    head == "+" && return Sum(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "-" && return Difference(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "*" && return Product(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "/" && return Division(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "^" && return Power(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "hole" && return Hole(parse(Int, sexp[2]))
    # Function application: (fname arg1 arg2 ...)
    FunctionApplication(FunctionSymbol(head),
        Tuple(_recon_term(sexp[i]) for i in 2:length(sexp)))
end

# ── Formula reconstruction ───────────────────────────────────────────────────

function _recon_formula(sexp::String)::Formula
    if endswith(sexp, "()")
        return PredicateApplication(PredicateSymbol(sexp[1:end-2]), ())
    end
    error("Unexpected atom in formula position: $sexp")
end

function _recon_formula(sexp::Vector)::Formula
    head = sexp[1]::String
    head == "Imp" && return Implies(_recon_formula(sexp[2]), _recon_formula(sexp[3]))
    head == "Not" && return Not(_recon_formula(sexp[2]))
    head == "All" && return Forall(Variable(sexp[2]::String), _recon_formula(sexp[3]))
    head == "Lt" && return LessThan(_recon_term(sexp[2]), _recon_term(sexp[3]))
    head == "Eq" && return Equals(_recon_term(sexp[2]), _recon_term(sexp[3]))
    # Predicate application: (PredName arg1 arg2 ...)
    PredicateApplication(PredicateSymbol(head),
        Tuple(_recon_term(sexp[i]) for i in 2:length(sexp)))
end

# ── Substitution reconstruction ──────────────────────────────────────────────

function _recon_substitution(sexp::Vector)
    fn_bindings = Dict{FunctionSymbol,Term}()
    pred_bindings = Dict{PredicateSymbol,Formula}()
    for binding in sexp
        tag = binding[1]::String
        name = binding[2]::String
        if tag == "fn"
            fn_bindings[FunctionSymbol(name)] = _recon_term(binding[3])
        elseif tag == "pred"
            pred_bindings[PredicateSymbol(name)] = _recon_formula(binding[3])
        else
            error("Unknown substitution binding tag: $tag")
        end
    end
    Substitution(fn_bindings, pred_bindings)
end

# ── Sequent reconstruction ───────────────────────────────────────────────────

function _recon_sequent(sexp::Vector)::Sequent
    ante = Tuple(_recon_formula(f) for f in sexp[1])
    cons = Tuple(_recon_formula(f) for f in sexp[2])
    Sequent(ante, cons)
end

# ── Replay: walk the certificate tree, re-execute through the kernel ─────────

function _replay(cert::Vector, sequent::Sequent)::Derivation
    tag = cert[1]::String

    if tag == "Open"
        return Derivation(Assume(sequent))

        # --- Right rules ---
    elseif tag == "ImpR"
        idx = parse(Int, cert[2]::String)
        ins = parse(Int, cert[3]::String)
        d = Derivation(ImpliesRightRule(sequent, Cons(idx), Ante(ins)))
        sub = _replay(cert[4], d.assumptions[1])
        Derivation(d, 1, sub)

    elseif tag == "NotR"
        idx = parse(Int, cert[2]::String)
        ins = parse(Int, cert[3]::String)
        d = Derivation(NotRightRule(sequent, Cons(idx), Ante(ins)))
        sub = _replay(cert[4], d.assumptions[1])
        Derivation(d, 1, sub)

    elseif tag == "AllR"
        idx = parse(Int, cert[2]::String)
        fresh = Variable(cert[3]::String)
        d = Derivation(ForallRightRule(sequent, Cons(idx), fresh))
        sub = _replay(cert[4], d.assumptions[1])
        Derivation(d, 1, sub)

        # --- Left rules ---
    elseif tag == "ImpL"
        idx = parse(Int, cert[2]::String)
        ins = parse(Int, cert[3]::String)
        d = Derivation(ImpliesLeftRule(sequent, Ante(idx), Cons(ins)))
        sub1 = _replay(cert[4], d.assumptions[1])
        d = Derivation(d, 1, sub1)
        sub2 = _replay(cert[5], d.assumptions[1])
        Derivation(d, 1, sub2)

    elseif tag == "NotL"
        idx = parse(Int, cert[2]::String)
        ins = parse(Int, cert[3]::String)
        d = Derivation(NotLeftRule(sequent, Ante(idx), Cons(ins)))
        sub = _replay(cert[4], d.assumptions[1])
        Derivation(d, 1, sub)



        # --- Structural rules ---
    elseif tag == "Close"
        target_ante = parse(Int, cert[2]::String)
        target_cons = parse(Int, cert[3]::String)
        Derivation(CloseRule(sequent, Ante(target_ante), Cons(target_cons)))

    elseif tag == "WL"
        idx = parse(Int, cert[2]::String)
        d = Derivation(WeakeningLeftRule(sequent, Ante(idx)))
        sub = _replay(cert[3], d.assumptions[1])
        Derivation(d, 1, sub)

    elseif tag == "WR"
        idx = parse(Int, cert[2]::String)
        d = Derivation(WeakeningRightRule(sequent, Cons(idx)))
        sub = _replay(cert[3], d.assumptions[1])
        Derivation(d, 1, sub)

    elseif tag == "Cut"
        cut_formula = _recon_formula(cert[2])
        ins_cons = parse(Int, cert[3]::String)
        ins_ante = parse(Int, cert[4]::String)
        d = Derivation(CutRule(sequent, cut_formula, Cons(ins_cons), Ante(ins_ante)))
        sub1 = _replay(cert[5], d.assumptions[1])
        d = Derivation(d, 1, sub1)
        sub2 = _replay(cert[6], d.assumptions[1])
        Derivation(d, 1, sub2)

    elseif tag == "Subst"
        pre_sequent = _recon_sequent(cert[2])
        σ = _recon_substitution(cert[3])
        d = Derivation(SubstitutionRule(pre_sequent, σ))
        # Kernel computes conclusion = substitute(pre_sequent, σ);
        # parent's combine step verifies it matches the target sequent.
        sub = _replay(cert[4], d.assumptions[1])
        Derivation(d, 1, sub)

        # --- Axiom ---
    elseif tag == "Axiom"
        formula = _recon_formula(cert[2])
        Derivation(AxiomRule(KernelAxiom(formula)))

        # --- Ground inequality ---
    elseif tag == "ArithR"
        left = _recon_term(cert[2])
        right = _recon_term(cert[3])
        Derivation(GroundInequalityRightRule(left, right))

    elseif tag == "ArithL"
        left = _recon_term(cert[2])
        right = _recon_term(cert[3])
        Derivation(GroundInequalityLeftRule(left, right))

    else
        error("Unknown rule tag in certificate: $tag")
    end
end

# Replay ignoring the sequent arg (for Axiom, ArithR/L at the root)
function _replay(cert::Vector, ::Nothing)::Derivation
    _replay(cert, Sequent((), ()))  # dummy; overridden by rule
end

# ── Public API ───────────────────────────────────────────────────────────────

"""
    deserialize_proof(text) -> Derivation

Parse an S-expression proof certificate and replay it through the
kernel, producing a fully verified `Derivation`.  Every rule
application is re-checked by the kernel constructors — if the
certificate is invalid the kernel will throw.
"""
function deserialize_proof(text::String)::Derivation
    sexp = _parse_sexp(text)
    # sexp = ["proof", [ante_list, cons_list], cert_tree]
    goal = _recon_sequent(sexp[2])
    d = _replay(sexp[3], goal)
    d.conclusion == goal ||
        error("Root conclusion mismatch: expected $goal, got $(d.conclusion)")
    d
end

end # module Serialization

