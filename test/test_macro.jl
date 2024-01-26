using Elenchos
@elenchos function max(x::Real, y::Real)
    @assert x > 0
    if x > y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x
end

@elenchos function simulate(x::Real, u::Real)
    @assert x >= 0
    @assert u >= x
    x = x + u
    @assert x >= 0
end

@elenchos function simulate(x::Real, z::Real)
    @assert z > 0
    @invariant x > 0
    while x < 10
        x = x + 1
    end
    @assert x > 0
end