# ═══════════════════════════════════════════════════════════════════════════════
#                    Arithmetic Solver (Farkas Engine)
#
# Bridges the gap between logical sequents and numerical optimization to
# find exact rational multiplier vectors for linear arithmetic proofs.
# ═══════════════════════════════════════════════════════════════════════════════

function linear_form(t::Term, variables::Vector{Variable})
    coeffs = coefficients(t)

    # Check that all non-constant terms are accounted for in our variable list
    for k in keys(coeffs)
        if k != ONE && k ∉ variables
            error("Expression is not linear with respect to the provided variables. Found: $k")
        end
    end

    a = Rational[get(coeffs, v, 0 // 1) for v in variables]
    b = get(coeffs, ONE, 0 // 1)
    return a, b
end

function linear_form(fml::Formula, v::Vector{Variable})
    if (leq = is_lessorequal_pattern(fml)) !== nothing
        lhs, rhs = leq
        a_coeffs, a_const = linear_form(lhs, v)
        b_coeffs, b_const = linear_form(rhs, v)
        return a_coeffs - b_coeffs, b_const - a_const
    end
end

function linear_form(seq::Sequent, target_idx::Int=1)
    # Compute the free variables of the sequent
    v = collect(free_variables(seq))
    n = length(v)
    m = length(seq.antecedent)

    # Pre-allocate A (m x n) and b (m)
    A = Matrix{Rational{Int}}(undef, m, n)
    b = Vector{Rational{Int}}(undef, m)

    for (i, h) in enumerate(seq.antecedent)
        result = linear_form(h, v)
        result === nothing && return nothing
        coeffs, const_val = result
        A[i, :] = coeffs
        b[i] = const_val
    end

    result = linear_form(seq.consequent[target_idx], v)
    result === nothing && return nothing
    g_coeffs, g_const = result

    return A, b, g_coeffs, g_const
end

"""
    select_independent_rows(A, row_indices, n)

Greedily select `n` linearly independent rows from `A[row_indices, :]`
using exact rational row-reduction.  Returns indices or `nothing`.
"""
function select_independent_rows(A::Matrix{Rational{BigInt}}, row_indices::Vector{Int}, n::Int)
    selected = Int[]
    U = Matrix{Rational{BigInt}}(undef, 0, size(A, 2))
    for idx in row_indices
        r = Rational{BigInt}.(A[idx, :])
        for k in 1:length(selected)
            # Identify the pivot column (first non-zero entry) of our k-th basis row
            pivot_col = findfirst(!iszero, U[k, :])
            if pivot_col !== nothing && r[pivot_col] != 0
                # Subtract the projection of U[k,:] from r to eliminate the entry at pivot_col
                # Equivalent to: r = r - r[pivot_col] * (U[k,:] .// U[k, pivot_col])
                r .-= (r[pivot_col] // U[k, pivot_col]) .* U[k, :]
            end
        end
        if any(!iszero, r)
            push!(selected, idx)
            U = vcat(U, r')
            length(selected) == n && return selected
        end
    end
    return nothing
end

"""
    exact_feasible(A, b, active, n_vars)

Solve the basis system A[basis,:] x = b[basis] exactly, choosing
linearly independent rows from `active`. Returns the rational solution
vector or `nothing` if verification fails.
"""
function exact_feasible(A::Matrix{Rational{BigInt}}, b::Vector{Rational{BigInt}},
    active::Vector{Int}, n_vars::Int)
    length(active) < n_vars && return nothing
    basis = select_independent_rows(A, active, n_vars)
    basis === nothing && return nothing
    x_exact = A[basis, :] \ b[basis]
    all(dot(A[i, :], x_exact) <= b[i] for i in 1:size(A, 1)) || return nothing
    return x_exact
end

"""
    farkas_witness(A, b, c; tol=1e-8)

Given hypotheses Ax ≤ b and direction c, find exact Farkas multipliers λ ≥ 0
that maximize cᵀx (minimize bᵀλ) exactly.

Returns `(λ_exact, obj_val)` or `nothing` if invalid.
"""
function farkas_witness(A, b, c; tol=1e-8)
    m, n = size(A)
    A_rat = Rational{BigInt}.(A)
    b_rat = Rational{BigInt}.(b)
    c_rat = Rational{BigInt}.(c)

    # 1. Solve primal LP numerically: max cᵀx s.t. Ax ≤ b
    model = Model(HiGHS.Optimizer)
    set_attribute(model, "output_flag", false)
    @variable(model, vars[1:n])
    cons = [@constraint(model, sum(Float64(A_rat[i, j]) * vars[j] for j in 1:n) <= Float64(b_rat[i])) for i in 1:m]
    @objective(model, Max, sum(Float64(c_rat[j]) * vars[j] for j in 1:n))
    optimize!(model)

    status = termination_status(model)
    status == MOI.OPTIMAL || return nothing

    # 2. Extract float duals → Farkas multipliers
    λ_float = [-dual(cons[i]) for i in 1:m]

    # 3. Exact recovery via basis recovery on dual constraint system
    #    Dual: min bᵀλ  s.t. Aᵀλ = c, λ ≥ 0
    #    Rewrite as: [Aᵀ; -Aᵀ; -I] λ ≤ [c; -c; 0]
    A_dual = vcat(A_rat', -A_rat', -Matrix{Int}(I, m, m))
    b_dual = vcat(c_rat, -c_rat, zeros(Int, m))

    slacks = Float64.(b_dual) .- A_dual * λ_float
    active = [i for i in 1:length(b_dual) if abs(slacks[i]) < tol]

    λ_exact = exact_feasible(A_dual, b_dual, active, m)
    λ_exact === nothing && return nothing

    # Compute exact objective value: obj = bᵀλ
    obj_val = dot(λ_exact, b_rat)
    return (λ_exact, obj_val)
end

function farkas_witness(seq::Sequent, target_idx::Int=1; tol=1e-8)
    result = linear_form(seq, target_idx)
    if result === nothing
        return nothing
    end
    A, b, c, d = result
    res = farkas_witness(A, b, c; tol=tol)
    res === nothing && return nothing
    λ, obj = res
    return Constant.(λ), Constant(obj)
end
