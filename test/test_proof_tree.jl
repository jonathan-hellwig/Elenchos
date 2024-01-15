using Elenchos: generate_graph, ProofFlowNode, AssertionNode, ProgramNode, BranchNode
body = quote end
body = MacroTools.prewalk(rmlines, body)
Test.@test generate_graph(body) == ProgramNode(:(), [])

body = quote
    x = 1
end
body = MacroTools.prewalk(rmlines, body)
Test.@test generate_graph(body) == ProgramNode(:(), [ProgramNode(:(x = 1), [])])

body = quote
    if true
    else
    end
end
body = MacroTools.prewalk(rmlines, body)
Test.@test generate_graph(body) == ProgramNode(:(), [BranchNode([:(true)], [])])

body = quote
    if true
        x = 1
    else
        x = 2
    end
    y = 1
end
body = MacroTools.prewalk(rmlines, body)
Test.@test generate_graph(body) == ProgramNode(:(()), ProofFlowNode[BranchNode(Union{Bool, Expr}[true], ProofFlowNode[ProgramNode(:(x = 1), ProofFlowNode[ProgramNode(:(y = 1), ProofFlowNode[])]), ProgramNode(:(x = 2), ProofFlowNode[ProgramNode(:(y = 1), ProofFlowNode[])])])])

body = quote
    @assert true
end
body = MacroTools.prewalk(rmlines, body)
Test.@test generate_graph(body) == ProgramNode(:(()), ProofFlowNode[AssertionNode([:(true)], ProofFlowNode[])])
