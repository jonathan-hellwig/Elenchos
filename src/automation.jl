# ═══════════════════════════════════════════════════════════════════════════════
#                    High-level Automation Tactics
# ═══════════════════════════════════════════════════════════════════════════════

# Automated linear arithmetic tactic for real-closed fields.
# Uses Farkas' Lemma to find coefficients for a linear combination of the
# hypotheses that implies the goal.
@tactic LinArith(target_idx::Union{Cons,First,Nothing}=Cons(1))
function Tactics.execute(t::LinArith, p::Derivation, subgoal_idx::Int)::Derivation
    seq = p.assumptions[subgoal_idx]
    # Resolve target: check that the formula at the given position is linear
    is_linear_target = f -> is_lessorequal_pattern(f) !== nothing
    loc = resolve_cons(t.target_idx, seq, is_linear_target)
    tidx = loc.idx

    # 1. Parse linear form to extract target bound 'd' for the chosen goal
    lin = linear_form(seq, tidx)
    lin === nothing && throw(TacticFailure("LinArith: Sequent is not linear: $seq"))
    _, _, _, d = lin

    # 2. Solve the LP to find Farkas multipliers
    result = farkas_witness(seq, tidx)
    if result === nothing
        throw(TacticFailure("LinArith: No Farkas witness found for sequent: $seq"))
    end
    λ, c_max = result

    # Check if the bound is sufficient: c_max <= d
    if c_max.value > d
        throw(TacticFailure("LinArith: Bound found ($(c_max.value)) is weaker than goal ($d)"))
    end
    # 3. Extract facts from antecedents and combine them
    combined_fact = λ' * ante(p, subgoal_idx=subgoal_idx)

    # 4. Chain the proof
    p = p |> trans(c_max, subgoal_idx=subgoal_idx, target_idx=t.target_idx)
    p = p |> apply(normalize(combined_fact), subgoal_idx=subgoal_idx)
    p = p |> Repeat(id())
    p = p |> ring_arith()

    return p
end
