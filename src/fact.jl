# ═══════════════════════════════════════════════════════════════════════════════
#                    Proof-Carrying Facts (Equalities & Inequalities)
#
# An `AbstractFact` pairs a formula with a closed `Derivation` proving it.
# Arithmetic on facts (scaling, addition, subtraction) produces new facts
# whose proofs are constructed from congruence axioms, maintaining soundness.
# ═══════════════════════════════════════════════════════════════════════════════

"""
    AbstractFact

Abstract supertype for proof-carrying facts.
Subtypes: `EqualityFact` (a ~ b) and `InequalityFact` (a ≤ b).
"""
abstract type AbstractFact end

# ═══════════════════════════════════════════════════════════════════════════════
#                    EqualityFact: Proof-Carrying Equality (a ~ b)
# ═══════════════════════════════════════════════════════════════════════════════

"""
    EqualityFact(eq::Equals)
    EqualityFact(eq::Equals, proof::Derivation)

A proof-carrying equality. Wraps an `Equals` formula together with a closed
`Derivation` that proves it.

The reflexivity constructor `EqualityFact(eq)` builds a trivial proof `eq ⊢ eq`.
The general constructor validates that the proof is closed (no open goals),
concludes `eq`, and has exactly one consequent formula.
"""
struct EqualityFact <: AbstractFact
    left::Term
    right::Term
    proof::Derivation

    function EqualityFact(eq::Equals)
        seq = Sequent((eq,), (eq,))
        p = start_proof(seq) |> id()
        return new(eq.left, eq.right, p)
    end

    function EqualityFact(left::Term, right::Term, p::Derivation)
        length(p.assumptions) == 0 ||
            error("Proof must be closed (no open assumptions)")
        eq = left ~ right
        p.conclusion.consequent[1] == eq ||
            error("Proof conclusion must match the equality")
        length(p.conclusion.consequent) == 1 ||
            error("Proof must have exactly one consequent formula")
        return new(left, right, p)
    end
end

Base.show(io::IO, t::EqualityFact) = print(io, "Fact(", t.left, " ~ ", t.right, ")")

# ─── EqualityFact Arithmetic ────────────────────────────────────────────────

"""Left-multiply: c · (a ~ b) → (c·a ~ c·b)."""
function Base.:(*)(c::Union{Number,Term}, t::EqualityFact)
    c_term = c isa Number ? Constant(c) : c
    target = (c_term * t.left) ~ (c_term * t.right)
    seq = Sequent(t.proof.conclusion.antecedent, (target,))
    p = start_proof(seq) |>
        apply(rule(THM_CONG_PRODUCT_RIGHT)) |>
        exact(t.proof)
    return EqualityFact(target.left, target.right, p)
end

"""Right-multiply: (a ~ b) · c → (a·c ~ b·c)."""
function Base.:(*)(t::EqualityFact, c::Union{Number,Term})
    c_term = c isa Number ? Constant(c) : c
    target = (t.left * c_term) ~ (t.right * c_term)
    seq = Sequent(t.proof.conclusion.antecedent, (target,))
    p = start_proof(seq) |>
        apply(rule(THM_CONG_PRODUCT_LEFT)) |>
        exact(t.proof)
    return EqualityFact(target.left, target.right, p)
end

"""
    _combine_binary(p1, p2, ax, pattern, target_fml) → Derivation

Internal helper for binary fact operations (+, -). Merges antecedents from
two proofs, applies a congruence axiom with conjunction premise, then closes
both subgoals.
"""
function _combine_binary(p1::Derivation, p2::Derivation, thm::Derivation,
    target_fml::Formula)
    ante1 = p1.conclusion.antecedent
    ante2 = p2.conclusion.antecedent
    seq = Sequent((ante1..., ante2...), (target_fml,))
    p = start_proof(seq) |>
        apply(rule(thm)) |>
        and_right()
    for _ in 1:length(ante2)
        p = p |> weaken_left(idx=Ante(length(ante1) + 1))
    end
    p = p |> exact(p1)
    for _ in 1:length(ante1)
        p = p |> weaken_left(idx=Ante(1))
    end
    p = p |> exact(p2)
    return p
end

"""Add: (a ~ b) + (c ~ d) → (a+c ~ b+d)."""
function Base.:(+)(t1::EqualityFact, t2::EqualityFact)
    target = (t1.left + t2.left) ~ (t1.right + t2.right)
    p = _combine_binary(t1.proof, t2.proof,
        THM_CONG_ADD_LEFT_RIGHT_EQUAL, target)
    EqualityFact(target.left, target.right, p)
end

"""Subtract: (a ~ b) - (c ~ d) → (a-c ~ b-d)."""
function Base.:(-)(t1::EqualityFact, t2::EqualityFact)
    target = (t1.left - t2.left) ~ (t1.right - t2.right)
    p = _combine_binary(t1.proof, t2.proof,
        THM_CONG_SUB_LEFT_RIGHT_EQUAL, target)
    EqualityFact(target.left, target.right, p)
end

function Base.:(-)(t::EqualityFact, c::Union{Number,Term})
    c_term = c isa Number ? Constant(c) : c
    p_c = start_proof(Sequent((), (c_term ~ c_term,))) |> apply(AX_EQ_REFL)
    f_c = EqualityFact(c_term, c_term, p_c)
    return t - f_c
end

function Base.:(-)(c::Union{Number,Term}, t::EqualityFact)
    c_term = c isa Number ? Constant(c) : c
    p_c = start_proof(Sequent((), (c_term ~ c_term,))) |> apply(AX_EQ_REFL)
    f_c = EqualityFact(c_term, c_term, p_c)
    return f_c - t
end

function Base.:(+)(t::EqualityFact, c::Union{Number,Term})
    c_term = c isa Number ? Constant(c) : c
    p_c = start_proof(Sequent((), (c_term ~ c_term,))) |> apply(AX_EQ_REFL)
    f_c = EqualityFact(c_term, c_term, p_c)
    return t + f_c
end

function Base.:(+)(c::Union{Number,Term}, t::EqualityFact)
    c_term = c isa Number ? Constant(c) : c
    p_c = start_proof(Sequent((), (c_term ~ c_term,))) |> apply(AX_EQ_REFL)
    f_c = EqualityFact(c_term, c_term, p_c)
    return f_c + t
end

"""Negate: -(a ~ b) → (-1·a ~ -1·b)."""
Base.:(-)(t::EqualityFact) = Constant(-1) * t

# ─── EqualityFact Normalization ──────────────────────────────────────────────

"""
    normalize(t::EqualityFact) → EqualityFact

Normalize both sides of a fact's equality, producing a new fact with a
proof that chains through the congruence of normalization.
"""
function normalize(t::EqualityFact)::EqualityFact
    norm_left, p_left = normalize(t.left)
    norm_right, p_right = normalize(t.right)
    norm_eq = norm_left ~ norm_right
    p = start_proof(Sequent(t.proof.conclusion.antecedent, (norm_eq,)))
    p = p |> rewrite_left(t.left)
    p = p |> weaken_all_but(t.left ~ norm_left)
    p = p |> exact(p_left)
    p = p |> rewrite_right(t.right)
    p = p |> weaken_all_but(t.right ~ norm_right)
    p = p |> exact(p_right)
    p = p |> exact(t.proof)
    return EqualityFact(norm_left, norm_right, p)
end

# ═══════════════════════════════════════════════════════════════════════════════
#                InequalityFact: Proof-Carrying Inequality (a ≤ b)
# ═══════════════════════════════════════════════════════════════════════════════

# ─── Trusted axioms for inequality manipulation ──────────────────────────────
# These are stated as KernelAxioms (trusted, not derived from primitives).



"""
    InequalityFact(lhs, rhs)
    InequalityFact(lhs, rhs, proof)

A proof-carrying inequality `lhs ≤ rhs`.

The reflexivity constructor `InequalityFact(a, b)` builds a trivial proof
`a ≤ b ⊢ a ≤ b`. The general constructor validates that the proof is
closed and its conclusion matches the inequality.
"""
struct InequalityFact <: AbstractFact
    left::Term
    right::Term
    proof::Derivation

    function InequalityFact(left::Term, right::Term)
        fml = left ≤ right
        seq = Sequent((fml,), (fml,))
        p = start_proof(seq) |> id()
        return new(left, right, p)
    end

    function InequalityFact(left::Term, right::Term, p::Derivation)
        length(p.assumptions) == 0 ||
            error("Proof must be closed (no open assumptions)")
        target = left ≤ right
        p.conclusion.consequent[1] == target ||
            error("Proof conclusion must match the inequality")
        length(p.conclusion.consequent) == 1 ||
            error("Proof must have exactly one consequent formula")
        return new(left, right, p)
    end
end

# Formula-based constructors: extract lhs/rhs from a ≤ pattern
function InequalityFact(fml::Formula)
    leq = is_lessorequal_pattern(fml)
    leq !== nothing || error("Formula must be a ≤ pattern, got: $fml")
    left, right = leq
    InequalityFact(left, right)
end

function InequalityFact(fml::Formula, p::Derivation)
    leq = is_lessorequal_pattern(fml)
    leq !== nothing || error("Formula must be a ≤ pattern, got: $fml")
    left, right = leq
    InequalityFact(left, right, p)
end

Base.show(io::IO, t::InequalityFact) = print(io, "Fact(", t.left, " ≤ ", t.right, ")")

# ─── InequalityFact Arithmetic ──────────────────────────────────────────────

"""Left-scale: c · (a ≤ b) → (c·a ≤ c·b). Sound only for c ≥ 0."""
function Base.:(*)(c::Union{Number,Term}, t::InequalityFact)
    c_num = c isa Number ? c : nothing
    c_term = c isa Number ? Constant(c) : c

    # If scaling by a negative constant, we MUST flip the terms to maintain ≤
    if c_num !== nothing && c_num < 0
        new_left, new_right = c_term * t.right, c_term * t.left
        ax = AX_LEQ_SCALE_LEFT_NEG
    else
        new_left, new_right = c_term * t.left, c_term * t.right
        ax = AX_LEQ_SCALE_LEFT
    end

    target = new_left ≤ new_right
    p = start_proof(Sequent(t.proof.conclusion.antecedent, (target,))) |>
        apply(ax) |> arith() |> exact(t.proof)

    return InequalityFact(new_left, new_right, p)
end


"""Right-scale: (a ≤ b) · c → (a·c ≤ b·c). Sound only for c ≥ 0."""
function Base.:(*)(t::InequalityFact, c::Union{Number,Term})
    c_num = c isa Number ? c : nothing
    c_term = c isa Number ? Constant(c) : c

    # If scaling by a negative constant, we MUST flip the terms to maintain ≤
    if c_num !== nothing && c_num < 0
        new_left, new_right = t.right * c_term, t.left * c_term
        ax = AX_LEQ_SCALE_RIGHT_NEG
    else
        new_left, new_right = t.left * c_term, t.right * c_term
        ax = AX_LEQ_SCALE_RIGHT
    end

    target = new_left ≤ new_right
    p = start_proof(Sequent(t.proof.conclusion.antecedent, (target,))) |>
        apply(ax) |>
        arith() |>
        exact(t.proof)
    return InequalityFact(new_left, new_right, p)
end

"""Add: (a ≤ b) + (c ≤ d) → (a+c ≤ b+d)."""
function Base.:(+)(t1::InequalityFact, t2::InequalityFact)
    new_left = t1.left + t2.left
    new_right = t1.right + t2.right
    target = new_left ≤ new_right
    p = _combine_binary(t1.proof, t2.proof, fwd_axiom(AX_LEQ_ADD), target)
    InequalityFact(new_left, new_right, p)
end

function Base.:(+)(t::InequalityFact, c::Union{Number,Term})
    c_term = c isa Number ? Constant(c) : c
    new_left = t.left + c_term
    new_right = t.right + c_term
    target = new_left ≤ new_right
    p = start_proof(c_term ≤ c_term) |> refl()
    p = _combine_binary(t.proof, p, fwd_axiom(AX_LEQ_ADD), target)
    InequalityFact(new_left, new_right, p)
end

function Base.:(+)(c::Union{Number,Term}, t::InequalityFact)
    c_term = c isa Number ? Constant(c) : c
    new_left = c_term + t.left
    new_right = c_term + t.right
    target = new_left ≤ new_right
    p = start_proof(c_term ≤ c_term) |> refl()
    p = _combine_binary(p, t.proof, fwd_axiom(AX_LEQ_ADD), target)
    InequalityFact(new_left, new_right, p)
end

function Base.:(-)(t1::InequalityFact, t2::InequalityFact)
    # Notice the "cross-subtraction" structure!
    new_left = t1.left - t2.right
    new_right = t1.right - t2.left
    target = new_left ≤ new_right

    p = _combine_binary(t1.proof, t2.proof, fwd_axiom(AX_LEQ_SUB), target)
    InequalityFact(new_left, new_right, p)
end


function Base.:(-)(t::InequalityFact, c::Union{Number,Term})
    c_term = c isa Number ? Constant(c) : c
    new_left = t.left - c_term
    new_right = t.right - c_term
    target = new_left ≤ new_right
    p = start_proof(c_term ≤ c_term) |> refl()
    p = _combine_binary(t.proof, p, fwd_axiom(AX_LEQ_SUB), target)
    InequalityFact(new_left, new_right, p)
end

function Base.:(-)(c::Union{Number,Term}, t::InequalityFact)
    c_term = c isa Number ? Constant(c) : c
    new_left = c_term - t.right
    new_right = c_term - t.left
    target = new_left ≤ new_right
    p = start_proof(c_term ≤ c_term) |> refl()
    p = _combine_binary(p, t.proof, fwd_axiom(AX_LEQ_SUB), target)
    InequalityFact(new_left, new_right, p)
end

function Fact(fml::Formula)
    if !isnothing(is_lessorequal_pattern(fml))
        return InequalityFact(fml)
    else
        return EqualityFact(fml)
    end
end

"""
    ante(p::Derivation, target_idx::Int; subgoal_idx::Int=1) -> Fact
    ante(p::Derivation; subgoal_idx::Int=1) -> Vector{Fact}

Extract one or all antecedents from a derivation's open subgoal as proof-carrying `Fact`s.
A `Fact` returned by `ante` represents the assumption `fml ⊢ fml` for an antecedent in the proof state,
allowing it to be manipulated via fact arithmetic before being applied back to the proof.
"""
function ante(p::Derivation, target_idx::Int; subgoal_idx::Int=1)
    return Fact(p.assumptions[subgoal_idx].antecedent[target_idx])
end

function ante(p::Derivation; subgoal_idx::Int=1)
    return [Fact(fml) for fml in p.assumptions[subgoal_idx].antecedent]
end

function ante(seq::Sequent)
    return [Fact(fml) for fml in seq.antecedent]
end

# ─── Symbolic Multi-Fact Linear Combinations ─────────────────────────────────
function normalize(t::InequalityFact)::InequalityFact
    norm_left, p_left = normalize(t.left)
    norm_right, p_right = normalize(t.right)
    norm_eq = norm_left ≤ norm_right
    p = start_proof(Sequent(t.proof.conclusion.antecedent, (norm_eq,)))
    p = p |> rewrite_left(t.left)
    p = p |> weaken_all_but(t.left ~ norm_left)
    p = p |> exact(p_left)
    p = p |> rewrite_right(t.right)
    p = p |> weaken_all_but(t.right ~ norm_right)
    p = p |> exact(p_right)
    p = p |> exact(t.proof)
    return InequalityFact(norm_left, norm_right, p)
end


function normalize_left(t::InequalityFact)::InequalityFact
    normalize(t - t.right)
end

function normalize_right(t::InequalityFact)::InequalityFact
    normalize(t - t.left)
end

# TODO: Add Repeat(id()) here.
function DerivedTactics.apply(f::AbstractFact; subgoal_idx::Int=1, target_idx::Union{Cons,Nothing}=Cons(1))
    Then(Choice(apply(f.proof; subgoal_idx=subgoal_idx, target_idx=target_idx), Then(zero_form(subgoal_idx=subgoal_idx, target_idx=target_idx), ring_norm(target_idx, subgoal_idx=subgoal_idx), apply(normalize(f - f.right).proof, subgoal_idx=subgoal_idx, target_idx=target_idx))),Repeat(id(subgoal_idx=nothing)))
end