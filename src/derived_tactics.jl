"""   Derived Tactics for Elenchos

Tactics that depend on unification or the strategy AST,
and therefore cannot live in BaseTactics.

Strategy builders live in strategies.jl (included below).

Contents:
  Tactics (structs via @tactic):
    `uapply`   — unifying variant of `apply`
    `axiom`    — apply a KernelAxiom

  Plain functions:
    `have`     — forward lemma construction
"""
module DerivedTactics

using ..Kernel
using ..Tactics
using ..Strategy: Choice, Then, Repeat
using ..Theorems: THM_EQ_ANTISYMMETRY, THM_EQ_TRANS, THM_EQ_SYMM, THM_LEQ_REFL
using ..Unification: unify, unify_subterm_formula, match_subterm_formula, unify_sequent, find_first_in_sequent, MatchSite, search_sequent
using ..Walkers: find_subterm_formula, all_matches_formula, children, reconstruct
using ..Syntax
using ..BaseTactics: start_proof, fwd_axiom, instantiate, rule, weaken_left_all_but
using ..BaseTactics: apply_rule, ApplyRule,
    apply, Apply,
    comm,
    rewrite, Rewrite, Order, NoOrder, TermOrder, MonomialOrder, term_lt,
    Id, ImpliesRight, ImpliesLeft, NotRight, NotLeft,
    AndLeft, AndRight, OrRight, Cut, Weaken,
    ArithLeft, ArithRight,
    Exact, Subst, WeakenAllBut,
    id, implies_right, implies_left, not_right, not_left,
    and_left, and_right, or_right, or_left, cut, weaken,
    arith_left, arith_right,
    exact, subst, weaken_all_but, weaken_right, weaken_left


export refl
export simplify, simplify_rfl
export ring_norm, ring_arith, prop
export symm, comm
export zero_form
export Arith, arith, congr, trans

# ═══════════════════════════════════════════════════════════════════════════════
#                         DERIVED TACTICS
# ═══════════════════════════════════════════════════════════════════════════════

"""
    have(target::Formula, rule::Derivation)

Forward lemma construction via unification.
Equivalent to `start_proof(target) |> uapply(rule)`.
"""
have(target::Formula, rule_deriv::Derivation) = start_proof(target) |> apply(rule_deriv)

@tactic Refl(target_idx::Union{Cons,First,Nothing}=First())
function Tactics.execute(t::Refl, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]
    is_reflexive = f -> begin
        if f isa Equals
            f.left == f.right
        elseif (leq = is_lessorequal_pattern(f)) !== nothing
            leq[1] == leq[2]
        else
            false
        end
    end
    tidx = resolve_cons(t.target_idx, seq, is_reflexive)

    ax = if seq.consequent[tidx.idx] isa Equals
        AX_EQ_REFL
    else
        THM_LEQ_REFL
    end
    return p |> apply(ax; target_idx=tidx, subgoal_idx=subgoal_idx)
end

@tactic Symm(target_idx::Union{Cons,First,Nothing}=First())
function Tactics.execute(t::Symm, p::Derivation, subgoal_idx::Int)::Derivation
    return p |> apply(THM_EQ_SYMM; target_idx=t.target_idx, subgoal_idx=subgoal_idx)
end

@tactic Trans(term::Term, target_idx::Union{Cons,First,Nothing}=First())
function Tactics.execute(t::Trans, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]
    tidx = resolve_cons(t.target_idx, seq, f -> f isa Equals || f isa LessThan || is_lessorequal_pattern(f) !== nothing)
    fml = seq.consequent[tidx.idx]

    if fml isa Equals
        σ = Substitution(_x_sym => fml.left, _y_sym => fml.right, _z_sym => t.term)
        p = p |> apply(instantiate(rule(THM_EQ_TRANS), σ); target_idx=tidx, subgoal_idx=subgoal_idx)
    elseif fml isa LessThan
        σ = Substitution(_x_sym => fml.left, _y_sym => fml.right, _z_sym => t.term)
        p = p |> apply(instantiate(rule(AX_LT_TRANS), σ); target_idx=tidx, subgoal_idx=subgoal_idx)
    elseif (leq = is_lessorequal_pattern(fml)) !== nothing
        σ = Substitution(_x_sym => leq[1], _y_sym => leq[2], _z_sym => t.term)
        p = p |> apply(instantiate(rule(AX_LEQ_TRANS), σ); target_idx=tidx, subgoal_idx=subgoal_idx)
    else
        throw(TacticFailure("Unsupported relation for transitivity: $fml"))
    end

    return p |> and_right(; subgoal_idx=subgoal_idx)
end

function trans(constant::Rational; target_idx::Union{Cons,First,Nothing}=First(), subgoal_idx::Union{Int,Nothing}=1)
    term = convert(Term, constant)
    return trans(term, target_idx=target_idx, subgoal_idx=subgoal_idx)
end

@tactic ArithEval(seq_pos::Union{SequentPosition,Nothing}=nothing)
function Tactics.execute(t::ArithEval, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]

    # 0. Bounds Check
    if t.seq_pos !== nothing
        side = t.seq_pos isa Ante ? seq.antecedent : seq.consequent
        if t.seq_pos.idx < 1 || t.seq_pos.idx > length(side)
            throw(TacticFailure("Position $(t.seq_pos) is out of bounds for $(t.seq_pos isa Ante ? "antecedent" : "consequent") of length $(length(side))."))
        end
    end

    # 1. Search for a ground term that isn't already a constant
    matches = search_sequent(seq, pos=t.seq_pos) do fml
        all_matches_formula(fml) do t
            (is_ground_term(t) && !(t isa Constant)) ? t : nothing
        end
    end

    it = iterate(matches)
    if isnothing(it)
        pos_info = t.seq_pos === nothing ? "" : " at position $(t.seq_pos)"
        throw(TacticFailure("No reducible ground term found$pos_info in sequent:\n$seq"))
    end
    site, _ = it

    lhs = site.data[1] # The ground term
    rhs = Constant(evaluate_ground_term(lhs))
    p = p |> rewrite(lhs => rhs, seq_pos=site.pos, subgoal_idx=subgoal_idx)
    p = p |> arith(; subgoal_idx=subgoal_idx)
    return p
end

@tactic Congr()
function Tactics.execute(t::Congr, p::Derivation, subgoal_idx::Int)::Derivation
    goal_eq = p.assumptions[subgoal_idx].consequent[1]
    goal_eq isa Equals || throw(TacticFailure("Congr requires an equality goal"))
    goal_lhs = goal_eq.left
    goal_rhs = goal_eq.right

    cs_lhs = children(goal_lhs)
    cs_rhs = children(goal_rhs)

    length(cs_lhs) == length(cs_rhs) || throw(TacticFailure("Terms have different numbers of children"))

    n = length(cs_lhs)
    diff_idx = Int[]
    for i in 1:n
        if cs_lhs[i] != cs_rhs[i]
            push!(diff_idx, i)
        end
    end

    # If identical, just use reflexivity
    if isempty(diff_idx)
        return p |> refl(subgoal_idx=subgoal_idx)
    end

    # Build intermediate bridging terms: T_k has the first k differences resolved to rhs
    T_terms = Term[goal_lhs]
    current_children = Term[cs_lhs...]
    for i in diff_idx
        current_children[i] = cs_rhs[i]
        push!(T_terms, reconstruct(goal_lhs, current_children...))
    end

    current_subgoal = subgoal_idx
    for step in 1:length(diff_idx)
        if step < length(diff_idx)
            # Bridge T_step with T_end using Transitivity to branch
            p = p |> trans(T_terms[step+1]; target_idx=Cons(1), subgoal_idx=current_subgoal)
        end

        d_idx = diff_idx[step]
        a_m = cs_lhs[d_idx]
        b_m = cs_rhs[d_idx]

        # Build context with a Hole at the differing position
        ctx_children = Term[]
        for j in 1:n
            if j < d_idx
                push!(ctx_children, cs_rhs[j])
            elseif j == d_idx
                push!(ctx_children, Hole(1))
            else
                push!(ctx_children, cs_lhs[j])
            end
        end
        ctx = reconstruct(goal_lhs, ctx_children...)

        σ = Substitution(_C_sym => ctx, _x_sym => a_m, _y_sym => b_m)

        # Leave a_m = b_m as an open goal for the user
        p = p |> cut(a_m ~ b_m; subgoal_idx=current_subgoal)
        # Weaken everything else away from the bridged branch and apply congruence
        p = p |> weaken_left_all_but(a_m ~ b_m; subgoal_idx=current_subgoal + 1)
        p = p |> exact(rule(AX_CONG_CONTEXT, σ); subgoal_idx=current_subgoal + 1)

        p = p |> weaken_right(fml=(T_terms[step] ~ T_terms[step+1]); subgoal_idx=current_subgoal)
        current_subgoal += 1
    end

    return p
end
function is_atomic_ground(fml::Formula)
    if fml isa Equals
        is_ground_term(fml.left) && is_ground_term(fml.right)
    elseif fml isa LessThan
        is_ground_term(fml.left) && is_ground_term(fml.right)
    elseif (leq = is_lessorequal_pattern(fml)) !== nothing
        is_ground_term(leq[1]) && is_ground_term(leq[2])
    else
        false
    end
end
@tactic Arith(target_idx::Union{Cons,First,Nothing}=First())
function Tactics.execute(t::Arith, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]
    tidx = resolve_cons(t.target_idx, seq, is_atomic_ground)
    fml = seq.consequent[tidx.idx]

    if fml isa Equals
        p = p |> apply(THM_EQ_ANTISYMMETRY; target_idx=tidx, subgoal_idx=subgoal_idx)
        p = p |> and_right(; subgoal_idx=subgoal_idx)
        p = p |> not_right(subgoal_idx=subgoal_idx)
        p = p |> arith_left(subgoal_idx=subgoal_idx)
        p = p |> not_right(subgoal_idx=subgoal_idx)
        p = p |> arith_left(subgoal_idx=subgoal_idx)
    elseif fml isa LessThan
        p = p |> arith_right(target_idx=tidx, subgoal_idx=subgoal_idx)
    elseif is_lessorequal_pattern(fml) !== nothing
        p = p |> not_right(target_idx=tidx, subgoal_idx=subgoal_idx)
        p = p |> arith_left(subgoal_idx=subgoal_idx)
    end

    return p
end

function is_atomic(fml::Formula)
    return fml isa Equals || fml isa LessThan || is_lessorequal_pattern(fml) !== nothing
end
@tactic ZeroForm(target_idx::Union{Cons,First,Nothing}=First())
function Tactics.execute(t::ZeroForm, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]
    tidx = resolve_cons(t.target_idx, seq, is_atomic)
    fml = seq.consequent[tidx.idx]

    if fml isa Equals
        return p |> apply(THM_SUB_ZERO_EQ, target_idx=tidx, subgoal_idx=subgoal_idx)
    elseif fml isa LessThan
        return p |> apply(AX_LT_SUB_TO_ZERO, target_idx=tidx, subgoal_idx=subgoal_idx)
    elseif (leq = is_lessorequal_pattern(fml)) !== nothing
        return p |> apply(AX_LEQ_SUB_TO_ZERO, target_idx=tidx, subgoal_idx=subgoal_idx)
    end
end
# ═══════════════════════════════════════════════════════════════════════════════
#                     STRATEGY BUILDERS
# ═══════════════════════════════════════════════════════════════════════════════

end # module DerivedTactics
