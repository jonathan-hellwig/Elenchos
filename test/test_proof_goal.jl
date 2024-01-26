using Elenchos: build_graph

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
    @invariant x > 0
    while true
        x = x + 1
    end
end
graphs = build_graph(body)
