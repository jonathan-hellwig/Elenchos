using Elenchos: extract, propagate_assertions, replace_assertions, build_goal_graph, Sequential, Empty, Assertion
import Test
using MacroTools

Test.@testset "Test extract" begin
    Test.@test extract(:(x = 1)) == (:x, 1.0)
    Test.@test extract(:(@assert x > 0)) == :(x > 0)

    body = quote 
        if x > 0
            x = 1
        else
            x = -1
        end
    end
    body = MacroTools.prewalk(rmlines, body).args[1]
    
    #TODO: Fix this test
    # Test.@test extract(body) == :(x > 0), Expr(:block,:(x = 1)), Expr(:block, :(x = -1))
end

Test.@testset "Test propagate assertions" begin
    body = quote
        @assert y < 0
        x = x + 1
        if x > 0
            x = 1
        else
            x = -1
            @assert x < 0
        end
        @assert x >= 0
    end
    propagate_assertions(body)

    body = quote
        @assert y < 0
        x = x + 1
        y = -x
        x = 1
        @assert x >= 0
    end
    propagate_assertions(body)

    body = quote
        @assert y < 0
        x = x + 1
        if x > 0
            x = 1
        else
            x = -1
            @assert x < 0
        end
        @assert x >= 0
    end
    graph = build_goal_graph(body)[1]
    assertions = propagate_assertions(body)
    replace_assertions(graph, assertions)
    
end

body = quote
    @assert y < 0
    x = x + 1
    if x > 0
        y = 1
    else
        x = -1
        @assert x < 0
    end
    @assert x >= 0
end
graphs = build_goal_graph(body)
assertions = propagate_assertions(body)

for i in eachindex(graphs)
    assertions = propagate_assertions(body)
    replace_assertions(graphs[i], assertions)
end
for graph in graphs
    println("Starting loop")
    previous_assertion = Assertion();
    for goal in graph
        if !isempty(goal.program)
            program = foldl(Sequential, goal.program)
            assumptions_ir = collect(previous_assertion.assertion)
            assertions_ir = collect(goal.assertion.assertion)
            println(assumptions_ir)
            println(program)
            println(assertions_ir)
        end
        previous_assertion = goal.assertion
    end
end


# TODO: Properly export a function that can be run symbolically
# In Gen, the author actually extended Base.Expr with :gentrace

body = quote
    @assert true
    if x > 0
        @assert x > 0
    else
        @assert x <= 0
    end
    @assert true
end

body = quote
    @assert y < 0
    @assert z < 0
end