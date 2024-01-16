include("macro.jl")
import Test
using MacroTools
# TODO:
# - create a graph data structure that keeps track of the goal graph 
# -> a goal struct with a vector of subgoals, a list of assumptions, a list of assertions and program
# -> the order of goals is important! if a goal fails to prove, all subsequent goals get discarded
# - create a function that takes a piece of code and returns a goal graph
# - implement loop invariants -> creates a new goal graph with @assert invariant loop_body @assert invariant
# - how to I deal with the _ in 1:T part of the loop?

# Should I create separate proof ir for the assertions and assumptions?
# This data structure should also keep track of invariants, i.e. some of the proof context

"""
@elenchos function simulate(T::Unsigned)
    @invariant x >= 0 
    for _ in 1:T
        x = x + 1
    end
    @assert x >= 0
end

ProofGoal([ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :(x = x + 1))], [ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :())])

@elenchos function simulate(T::Unsigned)
    @invariant x >= 0 
    for _ in 1:T
        x = x + 1
        @assert x >= 1
        x = x + 1
    end
    @assert x >= 0
end

Should I just always translate for _ in 1:T to while true?

ProofGoalNode([ProofGoalNode([ProofGoalLeaf([:(x >= 0)], [:(x >= 1)], :(x = x + 1)), ProofGoalLeaf([:(x >= 1)], [:(x >= 0)], :(x = x + 1))]), ProofGoalLeaf([:(x >= 0)], [:(x >= 0)], :())])

@elenchos function simulate(T::Unsigned)
    t = 0
    @invariant x >= 0
    while t < T
        t = t + 1
        x = x + 1
        @assert x >= 1
        x = x + 1
    end
    @assert x >= 0
end


"""

"""
for t in 1:10
end

is not the same as

t = 1
while t <= 10
    t = t + 1
end

What if loops are not used to iterate over a time range?

for x in [1,2,3]
end

This should not be allowed!
function sum(x::Real, y::Real)
    result = 0
    for s in [x, y]
        result = s + 1
    end
end

I will only support loops of the form:

for _ in 1:T
end

and translate them to:
{}*
"""

"""

What happens in the following case:

@elenchos function simulate(T::Unsigned)
    @assert x >= 0
    x = x + 1
    for _ in 1:T
        x = x + 1
        @assert x >= 0
    end
    @assert x >= 0
end

I.e. when there is an assertion in the loop body, but no loop invariant?
Only support assertion in loop body if there is a loop invariant?

"""

"""@invariant x > 0 for _ in 1:10
    x = x + 1
end

@invariant x > 0

@invariant x > 0 x = sum(x, y)

@invariant x > 0 begin
    x = x + 1
    x = x * x
end
"""

"""

function collect_assertions2(symbol_block)
    if isempty(symbol_block.args)
        return [[:(true)], [:(true)]]
    end
    # This does not work if assertions are nested in if statements
    program_not_empty = false
    last_is_assert = false
    assertions = []

    for x in symbol_block.args
        is_assert = isa(x, Expr) && @capture(x, @assert q_)
        if is_assert && !last_is_assert
            push!(assertions, Vector{Union{Expr,Bool}}([q]))
            last_is_assert = true
        elseif is_assert && last_is_assert
            push!(assertions[end], q)
        else
            last_is_assert = false
            program_not_empty = true
        end
    end
    # TODO: Fix the case where the program is empty
    is_assert = isa(symbol_block.args[1], Expr) && @capture(symbol_block.args[1], @assert q_)
    if is_assert && last_is_assert && !program_not_empty
        pushfirst!(assertions, [:(true)])
    else
        if !last_is_assert
            push!(assertions, [:(true)])
        end
        if !is_assert
            pushfirst!(assertions, [:(true)])
        end
    end
    return assertions
end

"""
# @elechnos function max(x::Real, y::Real)
#     @assert 0 <= x && 0 <= y
#     if x >= y
#         max_value = x
#     else
#         max_value = y
#     end
#     @assert max_value >= x && max_value >= y
#     @assert max_value == x || max_value == y
# end

# function_body = quote
#     @assert 0 <= x && 0 <= y
#     if x >= y
#         max_value = x
#         @assert max_value >= x
#         max_value = max_value + 1
#         @assert max_value >= y
#     else
#         max_value = y
#     end
#     @assert max_value >= x && max_value >= y
# end

# function_body = MacroTools.prewalk(rmlines, function_body)
# dump(function_body)

# function_body = quote
#     @assert 0 <= x && 0 <= y
#     if x >= y
#         @assert x >= y
#     else
#         max_value = y
#     end
#     @assert max_value >= x && max_value >= y
# end

# Try to separate assertions as much as possible to propagate them further down the graph
# Do the proof flow graph generation first, and then add additional nodes for the edge cases?
# It is not enough to just look at the first level of the program to determine if it needs to be split up

using MacroTools
import Test

abstract type ProofFlowNode end

mutable struct AssertionNode <: ProofFlowNode
    assertions::Vector{Union{Expr, Bool}}
    children::Vector{ProofFlowNode}
end

struct ProgramNode <: ProofFlowNode
    program::Expr
    children::Vector{ProofFlowNode}
end

struct BranchNode <: ProofFlowNode
    formulas::Vector{Union{Expr, Bool}}
    children::Vector{ProofFlowNode}
end

function Base.:(==)(x::ProofFlowNode, y::ProofFlowNode)
    if typeof(x) == typeof(y)
        if isa(x, AssertionNode)
            return x.assertions == y.assertions && x.children == y.children
        elseif isa(x, ProgramNode)
            return x.program == y.program && x.children == y.children
        elseif isa(x, BranchNode)
            return x.formulas == y.formulas && x.children == y.children
        end
    end
    return false
end

function parse_ast(ex, parent)
    if isa(ex, Expr)
        println(ex)
        if isempty(ex.args)
            return [parent]
        elseif ex.head == :(=)
            node = ProgramNode(ex, [])
            push!(parent.children, node)
            return [node]
        elseif ex.head == :macrocall && ex.args[1] == Symbol("@assert")
            println("assertion")
            println(ex)
            # TODO: There seems to be a bug, when removing line numbers for asserts, instead of 2 the index is 3
            node = AssertionNode([ex.args[3]], [])
            push!(parent.children, node)
            return [node]
        elseif ex.head == :block
            flows = Vector{ProofFlowNode}([parent])
            for x in ex.args
                current = popfirst!(flows)
                nodes = parse_ast(x, current)
                for flow in flows
                    push!(flow.children, nodes...)
                end
                append!(flows, nodes)
            end
            return flows
        elseif ex.head == :if
            branch_node = BranchNode([ex.args[1]], [])
            first_branch = parse_ast(ex.args[2], branch_node)
            second_branch = parse_ast(ex.args[3], branch_node)
            push!(parent.children, branch_node)
            return [first_branch..., second_branch...]
        end
    end
    error("Not expr ", ex)
end

function generate_graph(ex)
    root = ProgramNode(:(), [])
    parse_ast(ex, root)
    return root
end


function merge_assertions(root)
    if isa(root, AssertionNode)
        children = []
        for child in root.children
            if isa(child, AssertionNode)
                merge_assertions(child)
                append!(root.assertions, child.assertions)
                append!(children, child.children)
            else
                merge_assertions(child)
                push!(children, child)
            end
        end
        root.children = children
    end
end

function remove_node(root, node)
    if isa(root, AssertionNode)
        for child in root.children
            if child === node
                pop!(root.children, child)
            else
                remove_node(child, node)
            end
        end
    end
end

# TODO:
# - merge assertion nodes
#    - merge two subsequent assertion nodes
# - merge program nodes
#    - merge two subsequent program nodes
#    - do backtracking for branching nodes
# - translate graph to dl_ir graph
# Do I need a different data structure for the proof graph?

# Do I really need to merge programs? I could just explore the graph dfs and keep track of the current program
# It would be nice to have some kind of symbolic execution of the program and have vscode highlight, where the proof failed

struct ProofGoal
    assumptions::Vector{Formula}
    assertions::Vector{Formula}
    program::Program
end

function preprocess_graph(graph)
    merge_assertions(graph)
    # Simplify branching
    # Handle edge cases
    return graph
end

function generate_proof_goals(graph)
    return [ProofGoal([BoolTrue()], [BoolTrue()], Empty())]
end

graph = AssertionNode([:(true)], [ProgramNode(:(), [AssertionNode([:(true)], [])])])
Test.@test generate_proof_goals(graph) == [ProofGoal([BoolTrue()], [BoolTrue()], Empty())]

# How do I encode that a node has been visited?

test = Dict()
node = AssertionNode([:(true)], [])
test[node] = true

test[node]

body = quote
    x = 1
end
body = MacroTools.prewalk(rmlines, body)
test = program_to_dl_ir(body)
Sequential(test, test)

formula_to_dl_ir(true)