# Elenchos

Automated proving with tactics and strategies. Combines propositional logic, first-order reasoning, and linear arithmetic.

## Features

- **Tactics**: Manual proof construction (`implies_right`, `and_left`, `id`, etc.)
- **Strategies**: Automated search (DFS with backtracking, BFS, greedy)
- **Linear Arithmetic**: Automated proofs via Farkas witnesses
- **First-Order**: Universally quantified formulas with substitution
- **Serialization**: Export proofs as derivations or S-expressions

## Installation

```julia
using Pkg
Pkg.add(url="https://github.com/jonathan-hellwig/Elenchos.jl.git")
```

## Example

```julia
using Elenchos

# Simple propositional proof
p = start_proof(⊢ ((A → B) → A) → A)
p = p |> implies_right()
p = p |> implies_left()
p = p |> implies_right()
p = p |> id()

# Or use a strategy
strategy = Repeat(Choice(implies_right(), id()))
p = solve_dfs(strategy, start_proof(⊢ (A → (B → A))))

# Linear arithmetic
seq = ((x ≤ 2), (2*x ≤ 4)) ⊢ (x ≤ 3)
p = start_proof(seq) |> lin_arith()
```

## Documentation

See [examples/demo.jl](examples/demo.jl) for more use cases.

## License

MIT