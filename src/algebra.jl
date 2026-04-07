# ═══════════════════════════════════════════════════════════════════════════════
#                    Term Linear Algebra
#
# Extensions to Julia's Base and LinearAlgebra for symbolic Term types:
#   - Algebraic identity elements (zero, one)
#   - Type promotion and conversion rules
#   - Adjoint/transpose (no-ops for symbolic terms)
#   - Matrix–vector, matrix–matrix, and dot-product operations
#   - Exact rational nullspace computation via RREF
# ═══════════════════════════════════════════════════════════════════════════════


# ═══════════════════════════════════════════════════════════════════════════════
#                         Term Algebra Extensions
# ═══════════════════════════════════════════════════════════════════════════════

Base.zero(::Type{<:Term}) = ZERO
Base.zero(::Term) = ZERO
Base.one(::Type{<:Term}) = ONE
Base.one(::Term) = ONE
Base.promote_rule(::Type{<:Term}, ::Type{<:Term}) = Term
Base.promote_rule(::Type{<:Term}, ::Type{<:Number}) = Term
Base.convert(::Type{Term}, t::Term) = t
Base.convert(::Type{Term}, n::Number) = Constant(n)

LinearAlgebra.adjoint(t::Term) = t
Base.transpose(t::Term) = t

# ═══════════════════════════════════════════════════════════════════════════════
#                   Symbolic Matrix/Vector Multiplication
#
# Julia's generic linear algebra assumes numeric types with subtraction,
# which Terms don't support in the standard way. These specializations
# implement matrix–vector, matrix–matrix, and dot-product operations
# using only the overloaded +, * operators on Terms.
# ═══════════════════════════════════════════════════════════════════════════════

function Base.:*(A::AbstractMatrix{<:Term}, v::AbstractVector{<:Term})
    size(A, 2) == length(v) || throw(DimensionMismatch())
    res = Vector{Term}(undef, size(A, 1))
    for i in 1:size(A, 1)
        s = A[i, 1] * v[1]
        for j in 2:size(A, 2)
            s = s + A[i, j] * v[j]
        end
        res[i] = s
    end
    return length(res) == 1 ? res[1] : res
end

function Base.:*(A::AbstractMatrix{<:Term}, B::AbstractMatrix{<:Term})
    size(A, 2) == size(B, 1) || throw(DimensionMismatch())
    res = Matrix{Term}(undef, size(A, 1), size(B, 2))
    for i in 1:size(A, 1), j in 1:size(B, 2)
        s = A[i, 1] * B[1, j]
        for k in 2:size(A, 2)
            s = s + A[i, k] * B[k, j]
        end
        res[i, j] = s
    end
    return res
end

function Base.:*(u::Adjoint{<:Any,<:AbstractVector{<:Term}}, v::AbstractVector{<:Term})
    u_vec = u.parent
    length(u_vec) == length(v) || throw(DimensionMismatch())
    s = u_vec[1] * v[1]
    for i in 2:length(u_vec)
        s = s + u_vec[i] * v[i]
    end
    return s
end

function Base.:*(u::Adjoint{<:Any,<:AbstractVector{<:Term}}, A::AbstractMatrix{<:Term})
    u_vec = u.parent
    size(u_vec, 1) == size(A, 1) || throw(DimensionMismatch())
    res = Vector{Term}(undef, size(A, 2))
    for j in 1:size(A, 2)
        s = u_vec[1] * A[1, j]
        for i in 2:length(u_vec)
            s = s + u_vec[i] * A[i, j]
        end
        res[j] = s
    end
    return res'
end

# ═══════════════════════════════════════════════════════════════════════════════
#                    Exact Rational Nullspace (via RREF)
# ═══════════════════════════════════════════════════════════════════════════════

"""
    nullspace(M::AbstractMatrix{T}) → Matrix{T}

Compute the exact rational nullspace of `M` using row-reduced echelon form.
Returns a matrix whose columns form a basis for the nullspace, or an
empty matrix (cols=0) if the nullspace is trivial.
"""
function nullspace(M::AbstractMatrix{T}) where T
    rows, cols = size(M)
    S = promote_type(T, Rational{Int})
    R = rref(S.(M))

    # Identify pivot columns
    pivots = Int[]
    r = 1
    for c in 1:cols
        if r <= rows && R[r, c] == 1
            push!(pivots, c)
            r += 1
        end
    end

    # Build null basis: one vector per free column
    free_cols = setdiff(1:cols, pivots)
    null_basis = Vector{T}[]
    for f in free_cols
        v = zeros(T, cols)
        v[f] = 1
        for (i, p) in enumerate(pivots)
            v[p] = -R[i, f]
        end
        push!(null_basis, v)
    end

    return isempty(null_basis) ? zeros(T, cols, 0) : reduce(hcat, null_basis)
end


function coefficients(t::Term)
    acc = Dict{Term,Rational}()
    function canonicalize(e::Term)
        e isa Product || return e
        factors = Term[]
        function collect!(p::Term)
            if p isa Product
                collect!(p.left)
                collect!(p.right)
            else
                push!(factors, p)
            end
        end
        collect!(e)
        sort!(factors, by=(f -> f isa Variable ? f.name : string(f)))
        res = pop!(factors)
        while !isempty(factors)
            res = Product(pop!(factors), res)
        end
        return res
    end
    function walk!(e::Term, multiplier::Rational=1 // 1)
        if e isa Sum
            walk!(e.left, multiplier)
            walk!(e.right, multiplier)
        elseif e isa Product
            if e.left isa Constant
                walk!(e.right, multiplier * e.left.value)
            elseif e.right isa Constant
                walk!(e.left, multiplier * e.right.value)
            elseif e.left isa Sum
                walk!(e.left.left * e.right, multiplier)
                walk!(e.left.right * e.right, multiplier)
            elseif e.right isa Sum
                walk!(e.left * e.right.left, multiplier)
                walk!(e.left * e.right.right, multiplier)
            else
                k = canonicalize(e)
                acc[k] = get(acc, k, 0 // 1) + multiplier
            end
        elseif e isa Constant
            acc[ONE] = get(acc, ONE, 0 // 1) + multiplier * e.value
        else
            k = canonicalize(e)
            acc[k] = get(acc, k, 0 // 1) + multiplier
        end
    end
    walk!(t)
    return acc
end
