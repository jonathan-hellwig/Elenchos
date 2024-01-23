using Elenchos: extract, propagate_assertions, replace_assertions, build_goal_graph
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
    result = propagate_assertions(body)

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