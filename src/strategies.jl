module Strategies
# using ..Theorems: THM_ADD_ID_LEFT
# using ..Kernel: SequentPosition, KernelAxiom, Derivation, Cons, Ante
# using ..Strategy: Repeat, Choice, Then
# using ..DerivedTactics: arith_eval, rewrite

using ..Theorems: THM_ADD_ID_LEFT, THM_COLLECT_LEFT, THM_MUL_ZERO, THM_DIS_RIGHT, THM_MUL_ASSO_REV, THM_MUL_ID_LEFT, THM_EQ_ANTISYMMETRY, THM_MUL_LEFT_COMMUTATIVE, THM_ADD_LEFT_ASSOCIATIVE, THM_ADD_LEFT_COMMUTATIVE, THM_MUL_ZERO_LEFT
using ..Theorems: THM_COLLECT_BASE, THM_COLLECT_BASE_TAIL, THM_COLLECT_RIGHT, THM_COLLECT_LEFT_TAIL, THM_COLLECT_RIGHT_TAIL, THM_COLLECT_BOTH, THM_COLLECT_BOTH_TAIL
using ..Kernel: SequentPosition, KernelAxiom, Derivation, Cons, Ante, Equals
using ..Tactics: TacticFailure
using ..BaseTactics: id, implies_right, implies_left, not_right, not_left,
                     and_left, and_right, or_left, or_right
                     
using ..DerivedTactics: apply, rewrite, symm, refl, arith, arith_eval, zero_form, 
                        NoOrder, MonomialOrder
                        
using ..Strategy: Repeat, Choice, Then

using ..Syntax: AX_DIFF, AX_DIS, 
                AX_MUL_ASSO, AX_MUL_COMM,
                AX_ADD_ASSO, AX_ADD_COMM, 
                AX_MUL_ID, AX_ADD_ID

export prop, rewrite_axiom, simplify, simplify_rfl, ring_norm, ring_arith
"""
    prop()

Per-subgoal propositional strategy: decompose connectives and close by identity.
Handles `→`, `¬`, `∧`, `∨`.

Returns a `Choice(...)` strategy over all invertible propositional rules.
Pass directly to a solver to apply until fixpoint:

    (proof′, trace) = solve_dfs(prop(), proof)
"""
function prop()
    Choice(
        id(),
        implies_right(),
        not_right(),
        not_left(),
        and_left(),
        or_right(),
        and_right(),
        implies_left(),
        or_left(),
    )
end


function rewrite_axiom(ax::KernelAxiom; seq_pos::Union{SequentPosition,Nothing}=nothing, subgoal_idx::Int=1, order=NoOrder())
    # TODO: Derivations do not use rule by default. Therefore, derived axioms might not work by default.
    ax.formula isa Equals || throw(TacticFailure("Axiom formula must be an equality"))
    if seq_pos isa Cons || seq_pos === nothing
        return Then(
            rewrite(ax.formula.left => ax.formula.right, subgoal_idx=subgoal_idx, seq_pos=seq_pos, order=order),
            symm(subgoal_idx=subgoal_idx),
            apply(ax, subgoal_idx=subgoal_idx),
        )
    else
        return Then(
            rewrite(ax.formula.left => ax.formula.right, subgoal_idx=subgoal_idx, seq_pos=seq_pos, order=order),
            apply(ax, subgoal_idx=subgoal_idx),
        )
    end
end

function rewrite_axiom(thm::Derivation; seq_pos::Union{SequentPosition,Nothing}=nothing, subgoal_idx::Int=1, order=NoOrder())
    # TODO: Derivations do not use rule by default. Therefore, derived axioms might not work by default.
    fml = thm.conclusion.consequent[1]
    fml isa Equals || throw(TacticFailure("Axiom formula must be an equality"))
    if seq_pos isa Cons || seq_pos === nothing
        return Then(
            rewrite(fml.left => fml.right, subgoal_idx=subgoal_idx, seq_pos=seq_pos, order=order),
            symm(subgoal_idx=subgoal_idx),
            apply(thm, subgoal_idx=subgoal_idx),
        )
    else
        return Then(
            rewrite(fml.left => fml.right, subgoal_idx=subgoal_idx, seq_pos=seq_pos, order=order),
            apply(thm, subgoal_idx=subgoal_idx),
        )
    end
end

function simplify(axs::Union{KernelAxiom,Derivation}...; seq_pos=nothing, subgoal_idx=1, order=NoOrder())
    Repeat(Choice([rewrite_axiom(ax; seq_pos=seq_pos, subgoal_idx=subgoal_idx, order=order) for ax in axs]...))
end

function simplify_rfl(axs::KernelAxiom...; seq_pos=nothing, subgoal_idx=1, order=NoOrder())
    Then(simplify(axs...; seq_pos=seq_pos, subgoal_idx=subgoal_idx, order=order), refl(subgoal_idx=subgoal_idx))
end

function ring_norm(seq_pos::SequentPosition=Cons(1); subgoal_idx::Int=1)
    # ── Phase 1: Arithmetic crush ────────────────────────────────────────────
    arith_norm = Repeat(arith_eval(subgoal_idx=subgoal_idx))

    # ── Phase 1.5: Remove 0*x and x*0 ────────────────────────────────────────
    zero_elim = simplify(THM_MUL_ZERO, THM_MUL_ZERO_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 2: Difference elimination ──────────────────────────────────────
    diff_elim = simplify(AX_DIFF, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 3: Distributivity (expand products over sums) ──────────────────
    distribute = simplify(AX_DIS, THM_DIS_RIGHT, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 4: Right-associate products ─────────────────────────────────────
    mul_right_assoc = simplify(AX_MUL_ASSO, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 5: Sort factors (bubble sort on right-associated chains) ────────
    mul_sort = simplify(AX_MUL_COMM, THM_MUL_LEFT_COMMUTATIVE, seq_pos=seq_pos, subgoal_idx=subgoal_idx, order=MonomialOrder())

    # ── Phase 6: Left-associate products (for constant folding) ──────────────
    mul_left_assoc = simplify(THM_MUL_ASSO_REV, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 7: Fold constant prefixes ──────────────────────────────────────
    const_fold_mul = Repeat(arith_eval(subgoal_idx=subgoal_idx))

    # ── Phase 8: Right-associate products (canonical form) ───────────────────
    mul_right_assoc_final = simplify(AX_MUL_ASSO, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 9: Right-associate sums ────────────────────────────────────────
    add_right_assoc = simplify(AX_ADD_ASSO, seq_pos=seq_pos, subgoal_idx=subgoal_idx)

    # ── Phase 10: Sort summands by monomial order ─────────────────────────────
    add_sort = simplify(AX_ADD_COMM, THM_ADD_LEFT_COMMUTATIVE, seq_pos=seq_pos, subgoal_idx=subgoal_idx, order=MonomialOrder())

    # ── Phase 11: Like-term folding ──────────────────────────────────────────
    fold_like = Repeat(Choice(
        Then(rewrite_axiom(THM_COLLECT_BASE, seq_pos=seq_pos, subgoal_idx=subgoal_idx), mul_left_assoc),
        Then(rewrite_axiom(THM_COLLECT_BASE_TAIL, seq_pos=seq_pos, subgoal_idx=subgoal_idx), mul_left_assoc),
        rewrite_axiom(THM_COLLECT_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(THM_COLLECT_RIGHT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(THM_COLLECT_LEFT_TAIL, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(THM_COLLECT_RIGHT_TAIL, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(THM_COLLECT_BOTH, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(THM_COLLECT_BOTH_TAIL, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        arith_eval(subgoal_idx=subgoal_idx)
    ))

    # ── Phase 12a: Simplify new coefficient arithmetic ───────────────────────
    coeff_arith = Repeat(Choice(rewrite_axiom(THM_MUL_ASSO_REV, seq_pos=seq_pos, subgoal_idx=subgoal_idx), arith(subgoal_idx=subgoal_idx)))

    # ── Phase 12b: Cleanup identities ────────────────────────────────────────
    cleanup = Repeat(Choice(
        rewrite_axiom(AX_MUL_ID, seq_pos=seq_pos, subgoal_idx=subgoal_idx),         # x*1 → x
        rewrite_axiom(THM_MUL_ID_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),    # 1*x → x
        rewrite_axiom(THM_MUL_ZERO, seq_pos=seq_pos, subgoal_idx=subgoal_idx),             # x*0 → 0
        rewrite_axiom(THM_MUL_ZERO_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),        # 0*x → 0
        rewrite_axiom(AX_ADD_ID, seq_pos=seq_pos, subgoal_idx=subgoal_idx),          # x+0 → x
        rewrite_axiom(THM_ADD_ID_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),     # 0+x → x
        arith_eval(subgoal_idx=subgoal_idx),
    ))

    cleanup2 = Repeat(Choice(
        rewrite_axiom(THM_ADD_LEFT_ASSOCIATIVE, seq_pos=seq_pos, subgoal_idx=subgoal_idx),
        rewrite_axiom(AX_ADD_ID, seq_pos=seq_pos, subgoal_idx=subgoal_idx),          # x+0 → x
        rewrite_axiom(THM_ADD_ID_LEFT, seq_pos=seq_pos, subgoal_idx=subgoal_idx),     # 0+x → x
        arith_eval(subgoal_idx=subgoal_idx),
    ))

    # ── Compose all phases ───────────────────────────────────────────────────
    return Then(
        arith_norm,             # 1.  crush ground arithmetic
        zero_elim,
        diff_elim,              # 2.  eliminate subtraction
        distribute,             # 3.  expand products over sums
        mul_right_assoc,        # 4.  right-associate products
        mul_sort,               # 5.  sort factors
        mul_left_assoc,         # 6.  left-associate (for const folding)
        const_fold_mul,         # 7.  fold constant factors
        mul_right_assoc_final,  # 8.  right-associate (canonical form)
        add_right_assoc,        # 9.  right-associate sums
        add_sort,               # 10. sort summands (monomial order)
        coeff_arith,            # 11. simplify coefficients
        fold_like,              # 12. collect like terms
        coeff_arith,            # 13. simplify new coefficients
        cleanup,                # 14. remove identity elements
        cleanup2,
    )
end

function ring_arith(; target_idx::Cons=Cons(1), subgoal_idx::Int=1)
    Then(
        zero_form(target_idx=target_idx, subgoal_idx=subgoal_idx),
        ring_norm(target_idx, subgoal_idx=subgoal_idx),
        Repeat(arith(target_idx=target_idx, subgoal_idx=subgoal_idx))
    )
end

end