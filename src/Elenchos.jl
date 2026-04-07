module Elenchos
using LinearAlgebra
using JuMP
using HiGHS

# ═══════════════════════════════════════════════════════════════════════════════
#  Public API for Elenchos
#
#  Each submodule is also exported, so users can always reach internals via
#  qualified access  (e.g. Elenchos.Kernel.GroundInequalityRightRule).
#  The top-level exports below provide the "convenient" surface.
# ═══════════════════════════════════════════════════════════════════════════════

# ── Kernel ────────────────────────────────────────────────────────────────────
include("kernel.jl")
using .Kernel
export Kernel

# Types — terms
export Term, Variable, Constant, FunctionSymbol, FunctionApplication
export Sum, Difference, Product, Division, Power, Hole

# Types — formulas
export Formula, PredicateSymbol, PredicateApplication, LessThan
export Not, Implies, Forall                                     # primitive connectives
export And, Or, Exists, Iff                                     # defined connectives
export Equals                                                   # primitive equality
export LessOrEqual, GreaterOrEqual, GreaterThan                 # defined comparisons

# Types — proof objects
export Sequent, Derivation, KernelAxiom
export Ante, Cons, SequentPosition
export Substitution, substitute, free_variables
export apply_context

# Constants & axiom vocabulary
export ZERO, ONE
export _x_sym, _y_sym, _z_sym, _w_sym, _a_sym, _b_sym, _c_sym
export _x, _y, _z, _w, _a, _b, _c
export _P_sym, _Q_sym, _C_sym, _C

# Axioms — equality
export AX_EQ_REFL
export AX_CONG_PRED, AX_CONG_CONTEXT
# Axioms — field (real arithmetic)
export AX_ADD_LEFT_ASSOCIATIVE
export AX_ADD_ID, AX_ADD_INV
export AX_ADD_COMM, AX_ADD_ASSO
export AX_MUL_ID, AX_MUL_INV
export AX_MUL_COMM, AX_MUL_ASSO
export AX_DIS
export AX_DIFF
export KERNEL_FIELD_AXIOMS

# Axioms — order
export AX_LT_IRREFLEXIVITY, AX_LT_TRANS, AX_LT_TRICHOTOMY
export AX_LT_ADD, AX_LT_MUL_POS, AX_LEQ_SUB_TO_ZERO, AX_LT_SUB_TO_ZERO
export AX_LEQ_TRANS
export KERNEL_ORDER_AXIOMS


# ── Walkers ───────────────────────────────────────────────────────────────────
include("walkers.jl")
using .Walkers
export Walkers, is_lessorequal_pattern

# ── Unification ───────────────────────────────────────────────────────────────
include("unification.jl")
using .Unification
export Unification
export unify, unify_subterm_formula, unify_subterm_term, unify_formula, unify_term
export unify_sequent, find_first_in_sequent, MatchSite

# ── Syntax ────────────────────────────────────────────────────────────────────
include("syntax.jl")
using .Syntax
export Syntax
export @vars, @funcs, @preds
export ∧, ∨, →, ¬, ∀, ∃, ↔, ⊢
export print_proof_tree, rule_name

# ── Serialization ─────────────────────────────────────────────────────────────
include("serialization.jl")
using .Serialization
export Serialization
export serialize_proof, deserialize_proof

# ── Tactics infrastructure ────────────────────────────────────────────────────
include("tactics.jl")
using .Tactics
export Tactics
export @tactic, TacticFailure
export First, resolve_cons, resolve_ante

# ── Base Tactics ──────────────────────────────────────────────────────────────
include("base_tactics.jl")
using .BaseTactics
export BaseTactics

export id, implies_right, implies_left, not_right, not_left
export forall_right, forall_left
export and_right, and_left, or_right, or_left, cut, weaken_left, weaken_right
export arith_right, arith_left
export comm
export apply, apply_rule, exact, subst, weaken, weaken_all_but, weaken_left_all_but, weaken_right_all_but
export instantiate
export start_proof, fwd_axiom, fwd_implies_right, rule
export ImpliesRight, NotRight, NotLeft, AndLeft, OrRight, OrLeft, AndRight, ImpliesLeft, Id
export Order, NoOrder, TermOrder, MonomialOrder, term_lt, monomial_lt
export FindTarget, ExactMatch, ExactSubterm, Rewrite, rewrite


# ── Strategy ──────────────────────────────────────────────────────────────────
include("strategy.jl")
using .Strategy
export Strategy

export Then, Choice, Repeat, Skip
export solve_dfs, solve_bfs, solve_greedy, replay
export print_tactic_proof

# ── Derived Tactics ───────────────────────────────────────────────────────────
# ── Algebra & Solvers ─────────────────────────────────────────────────────────
include("algebra.jl")
include("arithmetic_solver.jl")
export farkas_witness

include("theorems.jl")
using .Theorems
export Theorems
export THM_CONG_SUM_LEFT, THM_CONG_SUM_RIGHT, THM_CONG_PRODUCT_LEFT, THM_CONG_PRODUCT_RIGHT, THM_CONG_ADD_LEFT_RIGHT_EQUAL, THM_CONG_SUB_LEFT_RIGHT_EQUAL
export THM_EQ_ANTISYMMETRY
export THM_ADD_ID_LEFT, THM_ADD_LEFT_ASSOCIATIVE, THM_ADD_LEFT_COMMUTATIVE
export THM_MUL_ID_LEFT, THM_MUL_ASSO_REV, THM_MUL_LEFT_COMMUTATIVE
export THM_DIS_RIGHT, THM_DIS_REV
export THM_MUL_ZERO_LEFT
export THM_EQ_SUB_ZERO, THM_EQ_TRANS
export THM_SUB_ZERO_EQ
export THM_COLLECT_BASE, THM_COLLECT_BASE_TAIL, THM_COLLECT_LEFT, THM_COLLECT_RIGHT, THM_COLLECT_LEFT_TAIL, THM_COLLECT_RIGHT_TAIL, THM_COLLECT_BOTH, THM_COLLECT_BOTH_TAIL

include("derived_tactics.jl")
using .DerivedTactics
export DerivedTactics

export apply, refl, symm, have, comm
export prop, prop_arith, rewrite_axiom, simplify_bottom_up, simplify_rfl, arith, ring_norm, trans, prop, congr
export ring_arith, zero_form, arith_eval

include("strategies.jl")
using .Strategies
export Strategies
# ── Theorems ──────────────────────────────────────────────────────────────────
# include("theorems.jl")
# using .Theorems
# export Theorems
# export THM_MUL_ID_LEFT

include("simplification.jl")
include("fact.jl")
export nullspace, coefficients, linear_form
export AbstractFact, EqualityFact, InequalityFact, Fact, normalize, normalize_left, normalize_right, ante
export AX_LEQ_ADD, AX_LEQ_SCALE_LEFT, AX_LEQ_SCALE_RIGHT, AX_LEQ_SCALE_LEFT_NEG, AX_LEQ_SCALE_RIGHT_NEG
include("automation.jl")
export LinArith, lin_arith
end # module Elenchos
