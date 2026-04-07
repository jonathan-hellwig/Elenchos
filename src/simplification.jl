"""
    fold_bottom_up(f, expr::Term)

Post-order fold: process children first, then apply f to parent.
"""
function fold_bottom_up(f, expr::Term)
    cs = children(expr)
    if isempty(cs)
        return f(expr, [])
    end
    child_results = [fold_bottom_up(f, c) for c in cs]
    f(expr, child_results)
end

# ═══════════════════════════════════════════════════════════════════════════════
#                            RULE SYSTEM
# ═══════════════════════════════════════════════════════════════════════════════

abstract type Rule end

struct RwRule <: Rule
    rewrite::Pair
    tactic::Tactic
    order::Order
    constraint::Tuple{Term,Function}
end

struct EvalRule <: Rule
    tactic::Tactic
end

EvalRule() = EvalRule(arith())

Rule(rewrite::Pair, tactic::Tactic, order::Order) = RwRule(rewrite, tactic, order, (Constant(0), term -> true))
Rule(rewrite::Pair, tactic::Tactic) = RwRule(rewrite, tactic, NoOrder(), (Constant(0), term -> true))

# ═══════════════════════════════════════════════════════════════════════════════
#                         RULE APPLICATION
# ═══════════════════════════════════════════════════════════════════════════════

function apply_rule(rule::RwRule, term::Term)::Union{Term,Nothing}
    σ = unify(rule.rewrite[1], term)
    isnothing(σ) && return nothing

    lhs = σ(rule.rewrite[1])
    rhs = σ(rule.rewrite[2])

    if !rule.constraint[2](σ(rule.constraint[1]))
        return nothing
    end

    if !rule.order(rhs, lhs)
        return nothing
    end

    return rhs
end

function apply_rule(rule::EvalRule, term::Term)::Union{Term,Nothing}
    if is_ground_term(term)
        new_term = Constant(evaluate_ground_term(term))
        new_term != term && return new_term
    end
    return nothing
end

# ═══════════════════════════════════════════════════════════════════════════════
#                      REWRITING AT NODE LEVEL
# ═══════════════════════════════════════════════════════════════════════════════

function rewrite_at_node(term::Term, child_results::Vector, rules::Vector)::Tuple{Term,Union{Derivation,Nothing}}
    if isempty(child_results)
        current = term
        accumulated_proof = nothing
    else
        simplified_children = [cr[1] for cr in child_results]
        current = reconstruct(term, simplified_children...)

        if term == current
            accumulated_proof = nothing
        else
            changed_proofs = [cr[2] for cr in child_results if cr[2] !== nothing]
            accumulated_proof = start_proof(term ~ current) |> congr()
            if !isempty(changed_proofs)
                accumulated_proof = accumulated_proof |> Then(exact.(changed_proofs)...)
            end
        end
    end

    while true
        rule_match = nothing
        for rule in rules
            match = apply_rule(rule, current)
            if !isnothing(match)
                rule_match = (rule, match)
                break
            end
        end

        isnothing(rule_match) && break

        rule, next = rule_match
        rule_proof = start_proof(current ~ next) |> rule.tactic
        if accumulated_proof === nothing
            accumulated_proof = rule_proof
        else
            accumulated_proof = start_proof(term ~ next) |> trans(current) |> exact(accumulated_proof) |> exact(rule_proof)
        end
        current = next
    end

    return (current, accumulated_proof)
end

# ═══════════════════════════════════════════════════════════════════════════════
#                        SIMPLIFICATION ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

function _simplify(expr::Term, rules::Vector)::Tuple{Term,Union{Derivation,Nothing}}
    """Single pass: bottom-up fold with saturation at each node."""
    fold_bottom_up((term, child_results) -> rewrite_at_node(term, child_results, rules), expr)
end

function simplify_bottom_up(term::Term, rules::Vector)::Tuple{Term,Derivation}
    """Fixpoint iteration: repeat simplification until convergence."""
    t_prev = term
    p_prev = start_proof(term ~ term) |> refl()
    while true
        curr, p = _simplify(t_prev, rules)
        curr == t_prev && return (curr, p_prev)
        p_tmp = start_proof(term ~ curr)
        p_tmp = p_tmp |> trans(t_prev)
        p_tmp = p_tmp |> exact(p_prev)
        p_tmp = p_tmp |> exact(p)
        p_prev = p_tmp
        t_prev = curr
    end
end

# ═══════════════════════════════════════════════════════════════════════════════
#                       PROOF COMPOSITION
# ═══════════════════════════════════════════════════════════════════════════════

function chain(ps::Vector{Derivation})::Derivation
    """Chain multiple equality proofs via transitivity."""
    p_acc = ps[1]
    for p in ps[2:end]
        acc_lhs = p_acc.conclusion.consequent[1].left
        next_lhs = p.conclusion.consequent[1].left
        next_rhs = p.conclusion.consequent[1].right
        p_acc = start_proof(acc_lhs ~ next_rhs) |> trans(next_lhs) |> exact(p_acc) |> exact(p)
    end
    return p_acc
end

# ═══════════════════════════════════════════════════════════════════════════════
#                    POLYNOMIAL NORMALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

function normalize(t::Term)::Tuple{Term,Derivation}
    """Apply complete normalization pipeline with full proof."""

    # Phase 1: Elimination (identity, zero, difference)
    add_zero_elim = [
        Rule(_x + 0 => _x, apply(AX_ADD_ID)),
        Rule(0 + _x => _x, apply(THM_ADD_ID_LEFT))
    ]
    mul_zero_elim = [
        Rule(_x * 0 => Constant(0), apply(THM_MUL_ZERO)),
        Rule(0 * _x => Constant(0), apply(THM_MUL_ZERO_LEFT))
    ]
    diff_elim = [Rule(_x - _y => _x + (-1) * _y, apply(AX_DIFF))]

    # Phase 2: Expansion (distributivity)
    distribute = [
        Rule(_x * (_y + _z) => _x * _y + _x * _z, apply(AX_DIS)),
        Rule((_y + _z) * _x => _y * _x + _z * _x, apply(THM_DIS_RIGHT))
    ]

    # Phase 3: Canonicalization (associativity, sorting)
    mul_right_assoc = [Rule((_x * _y) * _z => _x * (_y * _z), apply(AX_MUL_ASSO))]
    mul_sort = [
        Rule(_x * (_y * _z) => _y * (_x * _z), apply(THM_MUL_LEFT_COMMUTATIVE), MonomialOrder()),
        Rule(_x * _y => _y * _x, apply(AX_MUL_COMM), MonomialOrder())
    ]
    mul_associative_left = [Rule(_x * (_y * _z) => (_x * _y) * _z, apply(THM_MUL_ASSO_REV))]
    add_right_assoc = [Rule((_x + _y) + _z => _x + (_y + _z), apply(AX_ADD_ASSO))]
    add_sort = [
        Rule(_x + _y => _y + _x, apply(AX_ADD_COMM), MonomialOrder()),
        Rule(_x + (_y + _z) => _y + (_x + _z), apply(THM_ADD_LEFT_COMMUTATIVE), MonomialOrder())
    ]

    # Phase 4: Collection (like-term grouping)
    collect = [
        Rule(_x + _x => 2 * _x, apply(THM_COLLECT_BASE)),
        Rule(_x + (_x + _y) => 2 * _x + _y, apply(THM_COLLECT_BASE_TAIL)),
        Rule((_z * _x) + _x => ((_z + 1)) * _x, apply(THM_COLLECT_LEFT)),
        Rule(_x + (_z * _x) => ((1 + _z)) * _x, apply(THM_COLLECT_RIGHT)),
        Rule((_z * _x) + (_x + _y) => ((_z + 1)) * _x + _y, apply(THM_COLLECT_LEFT_TAIL)),
        Rule((_x + _y) + (_z * _x) => ((1 + _z)) * _x + _y, apply(THM_COLLECT_RIGHT_TAIL)),
        Rule((_z * _x) + (_a * _x) => ((_z + _a)) * _x, apply(THM_COLLECT_BOTH)),
        RwRule((_z * _x) + (_a * _x + _y) => ((_z + _a)) * _x + _y, apply(THM_COLLECT_BOTH_TAIL), NoOrder(), (_a, term -> term isa Constant)),
        EvalRule()
    ]

    cleanup_constants = [
        Rule(_x + (_y + _z) => (_x + _y) + _z, apply(THM_ADD_LEFT_ASSOCIATIVE)),
        Rule(_x * (_y * _z) => (_x * _y) * _z, apply(THM_MUL_ASSO_REV)),
        EvalRule()
    ]

    # Phase 5: Cleanup (final simplifications)
    cleanup = [
        Rule(1 * _x => _x, apply(AX_MUL_ID)),
        Rule(_x * 1 => _x, apply(THM_MUL_ID_LEFT))
    ]

    # Execute pipeline
    t, p1 = simplify_bottom_up(t, [mul_zero_elim..., diff_elim..., add_zero_elim..., distribute..., mul_right_assoc..., mul_sort...])
    t, p2 = simplify_bottom_up(t, [mul_associative_left..., EvalRule()])
    t, p3 = simplify_bottom_up(t, [mul_right_assoc..., add_right_assoc...])
    t, p4 = simplify_bottom_up(t, add_sort)
    t, p5 = simplify_bottom_up(t, [collect..., mul_zero_elim..., add_zero_elim...])
    t, p6 = simplify_bottom_up(t, cleanup_constants)
    t, p7 = simplify_bottom_up(t, add_right_assoc)
    t, p8 = simplify_bottom_up(t, [cleanup..., add_zero_elim...])
    t, p9 = simplify_bottom_up(t, [Rule((_x * _y) * _z => _x * (_y * _z), apply(AX_MUL_ASSO))])

    return t, chain([p1, p2, p3, p4, p5, p6, p7, p8, p9])
end