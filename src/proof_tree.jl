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
struct ProofGoal
    assumptions::Union{Vector{Formula}, Nothing}
    assertions::Union{Vector{Formula}, Nothing}
    program::Union{Program, Nothing}
    subgoals::Vector{ProofGoal}
end

ProofGoalLeaf(assumptions::Vector{Formula}, assertions::Vector{Formula}, program::Program) = ProofGoal(assumptions, assertions, program, [])
ProofGoalNode(subgoals::Vector{ProofGoal}) = ProofGoal(Nothing, Nothing, Nothing, subgoals)

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

Test.@test true

macro invariant(ex...)
    println(dump(ex))
end

@invariant x > 0 for _ in 1:10
    x = x + 1
end

@invariant x > 0

@invariant x > 0 x = sum(x, y)

@invariant x > 0 begin
    x = x + 1
    x = x * x
end


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

function build_proof_tree(function_body)

end

@elechnos function max(x::Real, y::Real)
    @assert 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
end

function_body = quote
    @assert 0 <= x && 0 <= y
    if x >= y
        max_value = x
        @assert max_value >= x
        max_value = max_value + 1
        @assert max_value >= y
    else
        max_value = y
    end
    @assert max_value >= x && max_value >= y
end

function_body = MacroTools.prewalk(rmlines, function_body)
dump(function_body)

function_body = quote
    @assert 0 <= x && 0 <= y
    if x >= y
        @assert x >= y
    else
        max_value = y
    end
    @assert max_value >= x && max_value >= y
end

# Try to separate assertions as much as possible to propagate them further down the graph
# Do the proof flow graph generation first, and then add additional nodes for the edge cases?
# It is not enough to just look at the first level of the program to determine if it needs to be split up

# struct ProofFlowGraphNode
#     assumptions::Vector{Formula}
#     assertions::Vector{Formula}
#     program::Program
#     subgoals::Vector{ProofFlowGraphNode}
# end

# I am not sure whether an explicit graph data structure is necessary or an implicit one is enough

include("macro.jl")

# import Test

# @enum ProofFlowNodeType PROGRAM ASSERTION

# struct ProofFlowNode
#     type::ProofFlowNodeType
#     assertions::Union{Vector{Expr}, Nothing}
#     program::Union{Expr, Nothing}
#     first_child::Union{ProofFlowNode, Nothing}
#     second_child::Union{ProofFlowNode, Nothing}
# end

# The vector of expressions might be causing the problem
# Base.:(==)(x::ProofFlowNode, y::ProofFlowNode) = x.type == y.type && x.assertions == y.assertions && x.program == y.program && x.first_child == y.first_child && x.second_child == y.second_child
# AssertionNode(assertions::Vector{Expr}, first_child::Union{ProofFlowNode, Nothing}, second_child::Union{ProofFlowNode, Nothing}) = ProofFlowNode(ASSERTION, assertions, nothing, first_child, second_child)
# ProgramNode(program::Expr, first_child::Union{ProofFlowNode, Nothing}) = ProofFlowNode(PROGRAM, nothing, program, first_child, nothing)

function build_proof_graph(function_body)
    if isempty(function_body.args)
        return ProgramNode(:(), nothing)
    end
    if isa(function_body.args[1], Expr) && @capture(function_body.args[1], @assert q_)
        return AssertionNode([q], build_proof_graph(Expr(:block, Expr(:block, function_body.args[2:end]...))), nothing)
    end
    return ProgramNode(function_body, nothing)
end

function_body = quote end
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == ProgramNode(:(), nothing)


function_body = quote
    x = 1
end
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == ProgramNode(function_body, nothing)

function_body = quote
    x = 1
    y = 2
end
function_body = Base.remove_linenums!(function_body)

# Should I already convert the assertions to dl_ir?

Test.@test build_proof_graph(function_body) == ProgramNode(function_body, nothing)

function_body = quote
    @assert x >= 0
    x = 1
end
sub_program = quote
    x = 1
end
sub_program = Base.remove_linenums!(sub_program)
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == AssertionNode([:(x >= 0)], ProgramNode(sub_program, nothing), nothing)

# Add an enum for matching

abstract type ProofFlowNode end

struct AssertionNode <: ProofFlowNode
    assertions::Vector{Expr}
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


if typeof(x) == typeof(y)
    if isa(x, AssertionNode)
        return x.assertions == y.assertions && x.children == y.children
    elseif isa(x, ProgramNode)
        return x.program == y.program && x.children == y.children
    end
end

# I am not sure if this function also outputs equality if the children are nonempty

function Base.:(==)(x::ProofFlowNode, y::ProofFlowNode)
    if typeof(x) == typeof(y)
        if isa(x, AssertionNode)
            return x.assertions == y.assertions && x.children == y.children
        elseif isa(x, ProgramNode)
            return x.program == y.program && x.children == y.children
        end
    end
    return false
end

# function Base.isequal(x::ProofFlowNode, y::ProofFlowNode)
#     if typeof(x) == typeof(y)
#         if isa(x, AssertionNode)
#             return x.assertions == y.assertions && x.children == y.children
#         elseif isa(x, ProgramNode)
#             return x.program == y.program && x.children == y.children
#         end
#     end
#     return false
# end
using MacroTools
import Test
# function build_proof_graph(function_body)
#     if isempty(function_body.args)
#         return ProgramNode(:(), Vector{ProofFlowNode}())
#     end
#     if isa(function_body.args[1], Expr) && @capture(function_body.args[1], @assert q_)
#         return AssertionNode([q], [build_proof_graph(Expr(:block, function_body.args[2:end]...))])
#     end
#     return ProgramNode(function_body, Vector{ProofFlowNode}())
# end

# I could explore one path at a time, and remember all the other paths that I have not explored yet
# If there is a way to identify assertions, I could join the paths again
# I would just need to keep track of all explored lines 
# And I would need a mechanism to get the next line to explore
function build_proof_graph(body)
    if isempty(body.args)
        return ProgramNode(:(), Vector{ProofFlowNode}())
    end

    q = body.args
    while !isempty(q)
        x = pop!(q)
        if isa(x, Expr) && @capture(x, @assert q_)

        end
    end
end

function_body = quote end
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == ProgramNode(:(), Vector{ProofFlowNode}())


function_body = quote
    x = 1
end
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == ProgramNode(function_body, [])

function_body = quote
    x = 1
    y = 2
end
function_body = Base.remove_linenums!(function_body)

# Should I already convert the assertions to dl_ir?

Test.@test build_proof_graph(function_body) == ProgramNode(function_body, [])

function_body = quote
    @assert x >= 0
    x = 1
end
sub_program = quote
    x = 1
end
sub_program = Base.remove_linenums!(sub_program)
function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == AssertionNode([:(x >= 0)], [ProgramNode(sub_program, [])])


function_body = quote
    @assert x >= 0
    @assert x >= 0
    x = 1
end
sub_program = quote
    x = 1
end
sub_program = Base.remove_linenums!(sub_program)
function_body = Base.remove_linenums!(function_body)

Test.@test build_proof_graph(function_body) == AssertionNode([:(x >= 0)], [AssertionNode([:(x >= 0)], [ProgramNode(sub_program, [])])])

function_body = quote
    x = 1
    @assert x >= 0
end

function_body = Base.remove_linenums!(function_body)
Test.@test build_proof_graph(function_body) == ProgramNode(function_body, [AssertionNode([:(x >= 0)], [])])


body = quote
    @assert x >= 0
    if x >= 0
        x = 1
    else
        x = 2
    end
    x = 1
    @assert x >= 0
end

body = MacroTools.prewalk(rmlines, body)

function count_lines(ex)
    println(ex)
    if typeof(ex) == LineNumberNode 
        return 1
    elseif !(typeof(ex) == Expr)
        println("not expr ", typeof(ex))
        return 0
    else
        return sum([count_lines(x) for x in ex.args])
    end
end

count_lines(body)

body = quote end


if typeof(ex) == LineNumberNode 
    return 1
elseif !isa(x, Expr)
    return 0
else
    return sum([count_lines(x) for x in ex.args])
end
[i for i in 1:2]

sum([count_lines(x) for x in ex.args])


# I think I need some explicit representation of the graph where I have a list of nodes and a list of edges
# Or I need some type of stack, where I keep track of assertion nodes that need to be added to other paths


# For the if I could just run on the first branch until I reach an assertion, and not add the assertion to the end of the first branch
# Then I run the second branch separately and create a new assertion node for both branches
# Both branches have the same parent
# Do I need to keep track of parents?

# I could implement splitting as the default behavior, and merge two branches only after they have been fully explored


# TODO: Check whether the edge cases actually need to be handled
function merge_symbol_blocks(first_block, second_block)
    if isempty(first_block.args)
        return second_block
    end
    if isempty(second_block.args)
        return first_block
    end
    return Expr(:block, first_block.args..., second_block.args...)
end

function build_proof_graph(body)
    # if isempty(body.args)
    #     return ProgramNode(:(), Vector{ProofFlowNode}())
    # end

    # is_assert = isa(body.args[1], Expr) && @capture(body.args[1], @assert q_)
    # if is_assert
    #     return AssertionNode([q], [build_proof_graph(Expr(:block, body.args[2:end]...))])
    # elseif body.head == :if
    #     first_branch = merge_symbol_blocks(body.args[2], body])
    #     return AssertionNode([:(true)], [build_proof_graph(body.args[2]), build_proof_graph(body.args[3])])
    # else
    #     program = [body.args[1]]
    #     for (index, x) in enumerate(body.args[2:end])
    #         is_assert = isa(x, Expr) && @capture(x, @assert q_)
    #         if !is_assert
    #             push!(program, x)
    #         else
    #             return ProgramNode(Expr(:block, program...), [build_proof_graph(Expr(:block, body.args[index+1:end]...))])
    #         end
    #     end
    # end

    if isempty(body.args)
        return ProgramNode(:(), Vector{ProofFlowNode}())
    end


    # Should I change this depending on the first line of the program?
    root = ProgramNode(:(), Vector{ProofFlowNode}())
    ast_queue = Vector{Tuple{Expr, ProofFlowNode}}()
    push!(ast_queue, (body, root))
    while !isempty(ast_queue)
        x, current = pop!(ast_queue)
        if isempty(x.args)
            continue
        end
        current_line = x.args[1]
        if isa(current_line, Expr) && @capture(current_line, @assert q_)
            push!(current.children, AssertionNode([q], Vector{ProofFlowNode}()))
            push!(ast_queue, (Expr(:block, x.args[2:end]...), current.children[end]))
        elseif current_line.head == :if
            first_branch = merge_symbol_blocks(current_line.args[2], x.args[4:end])
            if length(current_line.args) == 2
                push!(current.children, BranchNode([current_line.args[1]], Vector{ProofFlowNode}()))
            else
                second_branch = merge_symbol_blocks(current_line.args[3], x.args[4:end])
            end
            second_branch = merge_symbol_blocks(x.args[3], x.args[4:end])


            
        else
            program = [current_line]
            index = 2
            for y in x.args[2:end]
                is_assert = isa(y, Expr) && @capture(y, @assert q_)
                # This needs to be replaced if there is more than assertion and not assertion in the program
                if !is_assert
                    push!(program, y)
                else
                    break
                end
                index += 1
            end
            push!(current.children, ProgramNode(Expr(:block, program...), Vector{ProofFlowNode}()))
            push!(ast_queue, (Expr(:block, x.args[index:end]...), current.children[end]))
        end
    end
    return root
end

function_body = quote
    @assert x >= 0
    x = 1
end
function_body = MacroTools.prewalk(rmlines, function_body)
build_proof_graph(function_body)


function_body = quote
    @assert x >= 0
    x = 1
    y = 1
end
function_body = MacroTools.prewalk(rmlines, function_body)
build_proof_graph(function_body)


function_body = quote
    @assert x >= 0
    x = 1
    @assert x >= 0
end
function_body = MacroTools.prewalk(rmlines, function_body)
build_proof_graph(function_body)


body = quote
    @assert x >= 0
    if x >= 0
        x = 1
    else
        x = 2
    end
    x = 1
    @assert x >= 0
end

body = MacroTools.prewalk(rmlines, body)

body = quote
    if true
    else
    end
end
body = MacroTools.prewalk(rmlines, body)

function build_graph()

    function parse_ast(ex, parent)
        if isa(ex, Expr)
            if isempty(ex.args)
                return parent
            end
            if ex.head == :(=)
                push!(parent.children, ProgramNode(ex, []))
                return parent
            end
            if ex.head == :block
                for x in ex.args
                    parent = parse_ast(x, parent)
                end
                return parent
            end
        end
    end
end


# abstract type ProofFlowNode end

# struct AssertionNode <: ProofFlowNode
#     assertions::Vector{Expr}
#     children::Vector{ProofFlowNode}
# end

# struct ProgramNode <: ProofFlowNode
#     program::Expr
#     children::Vector{ProofFlowNode}
# end

# struct BranchNode <: ProofFlowNode
#     formulas::Vector{Union{Expr, Bool}}
#     children::Vector{ProofFlowNode}
# end
function parse_ast(ex, parent)
    if isa(ex, Expr)
        if isempty(ex.args)
            return parent
        end
        if ex.head == :(=)
            push!(parent.children, ProgramNode(ex, []))
            return parent
        end
        if ex.head == :block
            flows = Vector{ProofFlowNode}()
            push!(flows, parent)
            for x in ex.args
                N = length(flows)
                for i in 1:N
                    flows[i] = parse_ast(x, flows[i])
                end
                for _ in 1:N
                    current = popfirst!(flows)
                    for child in current.children
                        if isa(child, BranchNode)
                            append!(flows, child.children)
                        else
                            push!(flows, child)
                        end
                    end
                end
            end
            return parent
        end
        if ex.head == :if
            branch_node = BranchNode([ex.args[1]], [])
            branch_node = parse_ast(ex.args[2], branch_node)
            branch_node = parse_ast(ex.args[3], branch_node)
            push!(parent.children, branch_node)
            return parent
        end
    end
    println("Not expr ", ex)
end

function generate_graph(ex)
    root = ProgramNode(:(), [])
    parse_ast(ex, root)
    return root
end
body = quote
    x = 1
    t = 1
end
body = MacroTools.prewalk(rmlines, body)
generate_graph(body)

body = quote
    if true
    else
    end
end
body = MacroTools.prewalk(rmlines, body)
generate_graph(body)

body = quote
    if true
        x = 1
    else
        x = 2
    end
    y = 1
end
body = MacroTools.prewalk(rmlines, body)
graph = generate_graph(body)

body = quote
    if true
        if true
            x = 1
        else
            x = 2
        end
        x = 1
    else
        x = 2
    end
    y = 1
end

body = MacroTools.prewalk(rmlines, body)
generate_graph(body)


function parse_ast(ex, parent)
    if isa(ex, Expr)
        if isempty(ex.args)
            # What should I do here?
            return ProgramNode(:(), [])
        end
        if ex.head == :(=)
            return ProgramNode(ex, [])
        end
        if ex.head == :block
            next = Vector{ProofFlowNode}([parent])
            for x in ex.args
                current = popfirst!(next)
                push!(next, parse_ast(x, current))
                if isa(next[end], BranchNode)
                    # push!(parent.children, next)
                    push!(next, next[end].children...)
                end
                push!(current.children, next[end])
                # push!(parent.children, next)
                # current = next
            end
            return current
        end
        if ex.head == :if
            # TODO: Implement the different cases for if statements
            first_branch = parse_ast(ex.args[2], parent)
            second_branch = parse_ast(ex.args[3], parent)
            branch_node = BranchNode([ex.args[1]], [first_branch, second_branch])
            # push!(parent.children, branch_node)
            return branch_node
        end
    end
    println("Not expr ", ex)
end

function parse_ast(ex, parent)
    if isa(ex, Expr)
        if isempty(ex.args)
            node = ProgramNode(:(), [])
            push!(parent.children, node)
            return [node]
        end
        if ex.head == :(=)
            node = ProgramNode(ex, [])
            push!(parent.children, node)
            return [node]
        end
        if ex.head == :block
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
        end
        if ex.head == :if
            branch_node = BranchNode([ex.args[1]], [])
            first_branch = parse_ast(ex.args[2], branch_node)
            second_branch = parse_ast(ex.args[3], branch_node)
            push!(parent.children, branch_node)
            return [first_branch..., second_branch...]
        end
    end
    error("Not expr ", ex)
end

root = ProgramNode(:(), [])
body = quote
    x = 1
    t = 1
end
body = MacroTools.prewalk(rmlines, body)
parse_ast(body, root)
println(root)

body = quote
    if true
        x = 1
    else
        x = 2
    end
    y = 1
end
body = MacroTools.prewalk(rmlines, body)
root = ProgramNode(:(), [])
parse_ast(body, root)