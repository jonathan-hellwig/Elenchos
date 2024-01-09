# Elenchos
## Example
Julia input code:
```julia
@elenchos function max(x::Real, y::Real)
    @assert 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
end
```
Kyx output code:
```kyx
ArchiveEntry "test.kyx"
   ProgramVariables
      Real maxValue;
      Real y;
      Real x;
   End.
   Problem
      ((0 <= x & 0 <= y)) -> [{{?(x >= y); maxValue := x;  ∪ ?(!(x >= y)); maxValue := y; }; }] ((maxValue >= x & maxValue >= y) & (maxValue = x | maxValue = y) & (0 <= x & 0 <= y))
   End.
End.
```