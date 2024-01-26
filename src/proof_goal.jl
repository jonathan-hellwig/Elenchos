using MacroTools
import Test

mutable struct ProofGoal
    program::Vector{Expr}
    assertions::Vector{Expr}
    propagated_assertions::Vector{Expr}
    children::Vector{ProofGoal}
end
# Base.show(io::IO, proof_goal::ProofGoal) = print(io, "ProofGoal(", proof_goal.program, ", ", proof_goal.children, ")")
ProofGoal(assertions::Vector{Expr}) = ProofGoal(Expr[], assertions, [], ProofGoal[])
ProofGoal() = ProofGoal(Expr[], [], [], ProofGoal[])
Base.copy(proof_goal::ProofGoal) = ProofGoal(deepcopy(proof_goal.program), deepcopy(proof_goal.assertion_line), deepcopy(proof_goal.propagated_assertions), proof_goal.children)

@enum ProgramEnum ASSIGNMENT ASSERT CONDITIONAL LINENUMBER WHILE INVARIANT UNDEFINED
function match_expr(ex)
    if isa(ex, Expr)
        if ex.head == :(=)
            return ASSIGNMENT
        elseif ex.head == :macrocall && ex.args[1] == Symbol("@assert")
            return ASSERT
        elseif ex.head == :macrocall && ex.args[1] == Symbol("@invariant")
            return INVARIANT
        elseif ex.head == :if
            return CONDITIONAL
        elseif ex.head == :while
            return WHILE
        else 
            return UNDEFINED
        end
    end
    return LINENUMBER
end


function extract(instruction)
    if match_expr(instruction) == ASSIGNMENT
        symbol = instruction.args[1]
        @assert isa(symbol, Symbol)
        term = instruction.args[2]
        if !isa(term, Expr) && !isa(term, Symbol)
            return symbol, Float64(term)
        end
        return symbol, term
    elseif match_expr(instruction) == ASSERT || match_expr(instruction) == INVARIANT
        formula = instruction.args[3]
        return formula
    elseif match_expr(instruction) == CONDITIONAL
        @assert length(instruction.args) == 3 "Only if statements with else branches are supported!"
        formula = instruction.args[1]
        @assert formula.head == :call
        true_branch = instruction.args[2]
        @assert true_branch.head == :block
        false_branch = instruction.args[3]
        @assert false_branch.head == :block
        return formula, true_branch, false_branch
    elseif match_expr(instruction) == WHILE
        formula = instruction.args[1]
        block = instruction.args[2]
        return formula, block
    end
    error("Unsupported instruction!")
end

function split_top(program)
    @assert length(program.args) >= 2 "The program must contain a line number and an instruction!"
    return program.args[1], program.args[2], Expr(:block, program.args[3:end]...)
end

function split_bottom(ex::Expr)
    @assert length(ex.args) >= 2 "The program must contain a line number and an instruction!"
    return ex.args[end-1], ex.args[end], Expr(:block, ex.args[1:end-2]...)
end

function get_variables(ex::Expr)
    variables = Set{Symbol}()
    queue = Vector{Union{Symbol,Expr,Number}}([ex])
    while !isempty(queue)
        x = pop!(queue)
        if isa(x, Expr)
            push!(queue, x.args...)
        elseif isa(x, Symbol) && !(x in [:+, :-, :*, :/, :^, :<, :>, :<=, :>=, :(==), :!=, :&&, :||, :!])
            push!(variables, x)
        end
    end
    return variables
end
function get_assertions(dict, program::Expr)
    if isempty(program.args)
        return [], []
    end
    line_number, instruction, rest = split_bottom(program)
    if match_expr(instruction) == ASSIGNMENT
        assertions, modified = get_assertions(dict, rest)
        symbol, _ = extract(instruction)
        return assertions, vcat(modified, [symbol])
    elseif match_expr(instruction) == ASSERT
        assertions, modified = get_assertions(dict, rest)
        formula = extract(instruction)
        new_assertion = [formula]
        for assertion in Iterators.flatten(assertions)
            current_modified = get_variables(assertion)
            if isempty(intersect(current_modified, modified))
                push!(new_assertion, assertion)
            end
        end
        dict[line_number] = new_assertion
        return [new_assertion], []
    elseif match_expr(instruction) == CONDITIONAL
        formula, true_branch, false_branch = extract(instruction)
        true_branch = Expr(:block, rest.args..., true_branch.args...)
        false_branch = Expr(:block, rest.args..., false_branch.args...)
        true_assertions, true_modified = get_assertions(dict, true_branch)
        false_assertions, false_modified = get_assertions(dict, false_branch)

        modified = vcat(true_modified, false_modified)
        filtered_true_assertions = [filter(x -> !(get_variables(x) ⊆ modified), true_assertion) for true_assertion in true_assertions]
        filtered_false_assertions = [filter(x -> !(get_variables(x) ⊆ modified), false_assertion) for false_assertion in false_assertions]
        assertions = vcat(filtered_true_assertions, filtered_false_assertions)
        return assertions, modified
    elseif match_expr(instruction) == WHILE
        formula, block = extract(instruction)
        # The body of the loop has a line number node at the end
        block = Expr(:block, rest.args..., block.args[1:end-1]...)
        assertions, modified = get_assertions(dict, block)
        return assertions, modified
    end
    error("Unsupported instruction!")
end

function get_assertions(program::Expr)
    dict = Dict()
    get_assertions(dict, program)
    for (key, value) in dict
        dict[key] = unique(value)
    end
    return dict
end

function Base.iterate(pg::ProofGoal)
    return (pg, nothing), nothing
end

function Base.iterate(pg::ProofGoal, state_queue)
    if state_queue === nothing
        queue = Vector{Tuple{ProofGoal, Union{ProofGoal, Nothing}}}()
        push!(queue, (pg, nothing))
        visited = Set()
        push!(visited, pg)
        return (pg, nothing), (nothing, queue, visited)
    else
        state, queue, visited = state_queue
        while !isempty(queue)
            current_pg, parent = popfirst!(queue)
            children = current_pg.children
            for child in children
                if !(child in visited)
                    push!(visited, child)
                    push!(queue, (child, current_pg))
                end
            end
            return (current_pg, parent), (state, queue, visited)
        end
        return nothing
    end
end

Base.IteratorSize(::Type{ProofGoal}) = Base.SizeUnknown()

function build_graph(node::ProofGoal, program::Expr)
    if isempty(program.args)
        return [node]
    end
    line_number, instruction, rest = split_top(program)
    open = build_graph(node, rest)
    if match_expr(instruction) == ASSIGNMENT
        for goal in open
            pushfirst!(goal.program, instruction)
        end
        return open
    elseif match_expr(instruction) == ASSERT
        formula = extract(instruction)
        proof_goal = ProofGoal([formula])
        for goal in open
            push!(proof_goal.children, goal)
        end
        return [proof_goal]
    elseif match_expr(instruction) == INVARIANT
        # TODO: Allow multiple invariants in a row
        if isempty(rest.args)
            error("Invariant must be followed by a block!")
        elseif match_expr(rest.args[2]) != WHILE
            error("Invariant must be followed by a while loop!")
        end
        formula, loop_body = extract(rest.args[2])
        invariant = extract(instruction)
        postcondition = ProofGoal([invariant])
        for goal in open
            pushfirst!(goal.program, Expr(:test, :(!$formula)))
            push!(postcondition.children, goal)
        end

        # Ignore asserts inside the loop body
        append!(postcondition.program, [Expr(:test, formula), Expr(:block, loop_body.args[1:end-1]...)])
        
        precondition = ProofGoal([invariant])
        # push!(precondition.program, Expr(:test, formula))
        push!(precondition.children, postcondition)
        
        return [precondition]
    elseif match_expr(instruction) == CONDITIONAL
        formula, true_branch, false_branch = extract(instruction)
        new_open = []
        for goal in open
            # At this point I should do a shallow copy?
            true_open = build_graph(copy(goal), true_branch)
            false_open = build_graph(copy(goal), false_branch)
            for true_goal in true_open
                pushfirst!(true_goal.program, Expr(:test, formula))
            end
            for false_goal in false_open
                pushfirst!(false_goal.program, Expr(:test, :(!$formula)))
            end
            new_open = vcat(true_open, false_open, new_open)
        end
        return new_open
    elseif match_expr(instruction) == WHILE
        formula, block = extract(instruction)
        for goal in open
            loop = Expr(:loop, Expr(:block, Expr(:test, formula), block.args...))
            complete = Expr(:block, loop, Expr(:test, :(!$formula)))
            pushfirst!(goal.program, complete)
        end
        return open
    elseif match_expr(instruction) == UNDEFINED
        error("Expressions of type '$(instruction.head)' are not supported!")
    end
end
function build_graph(program::Expr)
    return build_graph(ProofGoal(), program)
end

# function modified_variables(body::Expr)
#     queue = [body]
#     variables = Set{Tuple{Symbol,Symbol}}()
#     while !isempty(queue)
#         x = pop!(queue)
#         #TODO: Check whether you need type inference
#         if @capture(x, y_ = e_)
#             push!(variables, (y, :Real))
#         elseif isa(x, Expr)
#             push!(queue, filter(z -> isa(z, Expr), x.args)...)
#         end
#     end
#     return variables
# end

# function propagate_assertions!(pg::ProofGoal)
#     for (child, parent) in pg
#         # if parent === nothing
#         #     continue
#         # end
#         # for assertion in parent.assertions
#         #     push!(child.assertions, assertion)
#         # end

#         if get_variables
#     end
# end