using MacroTools
import Test
abstract type ProofGoal end
mutable struct Assertion <: ProofGoal
    formula::Expr
    propagated::Set{Expr}
    line_number::LineNumberNode
    block_propagation::Bool
    modified_variables::Set{Symbol}
    children::Vector{ProofGoal}
end
Assertion(formula::Expr, line_number::LineNumberNode) = Assertion(formula, Set{Expr}(), line_number, false, Set{Symbol}(), ProofGoal[])

mutable struct PGProgram <: ProofGoal
    instructions::Vector{Expr}
    propagated::Set{Expr}
    children::Vector{ProofGoal}
end
PGProgram() = PGProgram(Expr[], Set{Expr}(), ProofGoal[])
PGProgram(child::ProofGoal) = PGProgram(Expr[], Set{Expr}(), [child])
Base.copy(pg::PGProgram) = PGProgram(copy(pg.instructions), copy(pg.propagated), pg.children)

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
function build_graph(node::ProofGoal, program::Expr)
    if isempty(program.args)
        return [node]
    end
    line_number, instruction, rest = split_top(program)
    if match_expr(instruction) == ASSIGNMENT
        open = build_graph(node, rest)
        for goal in open
            @assert isa(goal, PGProgram)
            pushfirst!(goal.instructions, instruction)
        end
        return open
    elseif match_expr(instruction) == ASSERT
        open = build_graph(node, rest)
        formula = extract(instruction)
        assertion = Assertion(formula, line_number)
        for goal in open
            push!(assertion.children, goal)
        end
        program = PGProgram(assertion)
        return [program]
    elseif match_expr(instruction) == INVARIANT
        # TODO: Allow multiple invariants in a row
        if isempty(rest.args)
            error("Invariant must be followed by a block!")
        elseif match_expr(rest.args[2]) != WHILE
            error("Invariant must be followed by a while loop!")
        end
        open = build_graph(node, Expr(:block, rest.args[3:end]...))

        formula, loop_body = extract(rest.args[2])
        invariant = extract(instruction)
        postcondition = Assertion(invariant, line_number)
        postcondition.block_propagation = true
        for goal in open
            pushfirst!(goal.instructions, Expr(:test, :(!$formula)))
            push!(postcondition.children, goal)
        end
        loop_program = PGProgram(postcondition)
        # Ignore asserts inside the loop body
        append!(loop_program.instructions, [Expr(:test, formula), Expr(:block, loop_body.args[1:end-1]...)])
        
        precondition = Assertion(invariant, line_number)
        precondition.block_propagation = true
        # push!(precondition.program, Expr(:test, formula))
        push!(precondition.children, loop_program)
        
        return [PGProgram(precondition)]
    elseif match_expr(instruction) == CONDITIONAL
        open = build_graph(node, rest)
        formula, true_branch, false_branch = extract(instruction)
        new_open = []
        for goal in open
            # At this point I should do a shallow copy?
            true_open = build_graph(copy(goal), true_branch)
            false_open = build_graph(copy(goal), false_branch)
            for true_goal in true_open
                pushfirst!(true_goal.instructions, Expr(:test, formula))
            end
            for false_goal in false_open
                pushfirst!(false_goal.instructions, Expr(:test, :(!$formula)))
            end
            new_open = vcat(true_open, false_open, new_open)
        end
        return new_open
    elseif match_expr(instruction) == WHILE
        open = build_graph(node, rest)
        formula, block = extract(instruction)
        for goal in open
            loop = Expr(:loop, Expr(:block, Expr(:test, formula), block.args...))
            complete = Expr(:block, loop, Expr(:test, :(!$formula)))
            pushfirst!(goal.instructions, complete)
        end
        return open
    elseif match_expr(instruction) == UNDEFINED
        error("Expressions of type '$(instruction.head)' are not supported!")
    end
end
function build_graph(program::Expr)
    return build_graph(PGProgram(), program)
end

function modified_variables(body::Expr)
    queue = [body]
    variables = Set{Symbol}()
    while !isempty(queue)
        x = pop!(queue)
        #TODO: Check whether you need type inference
        if @capture(x, y_ = e_)
            push!(variables, y)
        elseif isa(x, Expr)
            push!(queue, filter(z -> isa(z, Expr), x.args)...)
        end
    end
    return variables
end

function propagate_modified(pg::ProofGoal)
    if isa(pg, Assertion)
        for child in pg.children
            propagate_modified(child)
        end
        return
    elseif isa(pg, PGProgram)
        modified = modified_variables(Expr(:block, pg.instructions...))
        for child in pg.children
            child.modified_variables = modified ∪ child.modified_variables
            propagate_modified(child)
        end
        return
    end
end

function propagate_assertions(pg::ProofGoal)
    if isa(pg, Assertion)
        for child in pg.children
            @assert isa(child, PGProgram)
            child.propagated = child.propagated ∪ pg.propagated 
            if !pg.block_propagation
                child.propagated = child.propagated ∪ Set([pg.formula])
            end
            propagate_assertions(child)
        end
    elseif isa(pg, PGProgram)
        for child in pg.children
            @assert isa(child, Assertion)
            for formula in pg.propagated
                if isempty(get_variables(formula) ∩ child.modified_variables) 
                    push!(child.propagated, formula)
                end
            end
            propagate_assertions(child)
        end
    end
end


function proof_obligations(pg::ProofGoal, obligations)
    # println(pg.children)
    if isa(pg, PGProgram)
        for child in pg.children
            @assert isa(child, Assertion)
            proof_obligations(child, obligations)
        end
    elseif isa(pg, Assertion)
        for program in pg.children
            @assert isa(program, PGProgram)
            for assertion in program.children
                if !isempty(program.instructions)
                    # println("LOWEST LEVEL")
                    @assert isa(assertion, Assertion)
                    assumptions = Set([pg.formula]) ∪ pg.propagated
                    program = Expr(:block, program.instructions...)
                    assertions = Set([assertion.formula]) ∪ assertion.propagated
                    push!(obligations, (assumptions, assertions, program, assertion.line_number))
                    # println(obligations)
                end
                proof_obligations(assertion, obligations)
            end
        end
    end
end

function proof_obligations(graph)
    obligations = []
    proof_obligations(graph, obligations)
    return obligations
end