using Elenchos: build_graph, propagate_modified, propagate_assertions, proof_obligations, formula_to_dl_ir, program_to_dl_ir

body = quote
    x = 1
    y = 2
    z = 3
    @assert x == y
end
build_graph(body)

body = quote
    while true
        x = x + 1
    end
end
build_graph(body)


body = quote
    @assert z > 0
    @invariant x > 0
    while true
        x = x + 1
    end
    @assert q > 0
end
graphs = build_graph(body)

for graph in graphs
    propagate_modified(graph)
end

for graph in graphs
    propagate_assertions(graph)
end
obligations = []
provables = Iterators.flatmap(x -> proof_obligations(x), graphs)
obligations
# proof_obligations(graphs[1], obligations)

for provable in provables
    name = hash(provable)
    assumptions, assertions, program = provable
    assumptions_ir = map(x -> formula_to_dl_ir(x), collect(assumptions))
    assertions_ir = map(x -> formula_to_dl_ir(x), collect(assertions))
    program = program_to_dl_ir(program)
    println(assumptions_ir)
    println(program)
    println(assertions_ir)
end