include("macro.jl")
using MacroTools
import Test

mutable struct Assertion
    line_number::LineNumberNode
    assertion::Set{Formula}
end

mutable struct ProofGoal
    program::Vector{Program}
    assertion::Assertion
    children::Vector{ProofGoal}
end

Base.copy(proof_goal::ProofGoal) = ProofGoal(deepcopy(proof_goal.program), deepcopy(proof_goal.assertion), proof_goal.children)
function ProofGoal(assertion)

    return ProofGoal(Vector{Program}(), assertion, Vector{ProofGoal}())
end

@enum ProgramEnum ASSIGNMENT ASSERT CONDITIONAL LINENUMBER
function match_expr(ex)
    if isa(ex, Expr)
        if ex.head == :(=)
            return ASSIGNMENT
        elseif ex.head == :macrocall && ex.args[1] == Symbol("@assert")
            return ASSERT
        elseif ex.head == :if
            return CONDITIONAL
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
            term = Float64(term)
        end
        return symbol, term
    elseif match_expr(instruction) == ASSERT
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
    else
        error("Unsupported instruction!")
    end
end

function split_top(program)
    @assert length(program.args) >= 2 "The program must contain a line number and an instruction!"
    return program.args[1], program.args[2], Expr(:block, program.args[3:end]...)
end

function precondition(program::Expr, postcondition::ProofGoal)
    if isempty(program.args)
        return [postcondition]
    end
    line_number, instruction, rest = split_top(program)
    open = precondition(rest, postcondition)
    if match_expr(instruction) == ASSIGNMENT
        for goal in open
            assignment = program_to_dl_ir(instruction)
            pushfirst!(goal.program, assignment)
        end
        return open
    elseif match_expr(instruction) == ASSERT
        formula = extract(instruction)
        assertion = Assertion(line_number, Set([formula_to_dl_ir(formula)]))
        proof_goal = ProofGoal(assertion)
        for goal in open
            push!(proof_goal.children, goal)
        end
        return [proof_goal]
    elseif match_expr(instruction) == CONDITIONAL
        formula, true_branch, false_branch = extract(instruction)
        formula = formula_to_dl_ir(formula)
        new_open = []
        for goal in open
            # At this point I should do a shallow copy?
            true_open = precondition(true_branch, copy(goal))
            false_open = precondition(false_branch, copy(goal))
            for true_goal in true_open
                pushfirst!(true_goal.program, DlTest(formula))
            end
            for false_goal in false_open
                pushfirst!(false_goal.program, DlTest(Not(formula)))
            end
            new_open = vcat(true_open, false_open, new_open)
        end
        return new_open
    end
end

function build_goal_graph(program::Expr)
    return precondition(program, ProofGoal(Assertion(LineNumberNode(1), Set([BoolTrue()]))))
end

function split_bottom(ex::Expr)
    @assert length(ex.args) >= 2 "The program must contain a line number and an instruction!"
    return ex.args[end-1], ex.args[end], Expr(:block, ex.args[1:end-2]...)
end

function propagate_assertions(ex::Expr)
    collected_assertions = Dict()
    function propagate_assertions(ex::Expr, modified_variables)
        if isempty(ex.args)
            return [], []
        end
        line_number, instruction, rest = split_bottom(ex)
        modified_variables, assertions = propagate_assertions(rest, modified_variables)
        if match_expr(instruction) == ASSIGNMENT
            symbol, _ = extract(instruction)
            push!(modified_variables, symbol)
            return modified_variables, assertions
        elseif match_expr(instruction) == ASSERT
            current_assertion = Assertion(line_number, Set([formula_to_dl_ir(extract(instruction))]))
            for assertion in assertions
                for formula in assertion.assertion
                    if modified_variables ∩ get_variables(formula) == []
                        push!(current_assertion.assertion, formula)
                    end
                end
            end
            collected_assertions[line_number] = current_assertion
            return [], [current_assertion]
        elseif match_expr(instruction) == CONDITIONAL
            formula, true_branch, false_branch = extract(instruction)
            # This is inefficient, could be improved by some explicit checking
            prepend!(true_branch.args, rest.args)
            prepend!(false_branch.args, rest.args)
            formula = formula_to_dl_ir(formula)
            true_modified_variables, true_assertion = propagate_assertions(true_branch, modified_variables)
            false_modified_variables, false_assertion = propagate_assertions(false_branch, modified_variables)
            modified_variables = true_modified_variables ∪ false_modified_variables
            # TODO: Make this less ugly
            formulas = [assertion.assertion for assertion in [true_assertion..., false_assertion...]]
            formulas = reduce((x, y) -> intersect(x, y), formulas)
            assertions = [Assertion(line_number, formulas)]
            return modified_variables, assertions
        end
    end
    modified_variables, assertions = propagate_assertions(ex, [])
    return collected_assertions
end

function replace_assertions(graph, assertions)
    for child in graph.children
        replace_assertions(child, assertions)
    end
    for assertion in values(assertions)
        if assertion.line_number == graph.assertion.line_number
            graph.assertion = deepcopy(assertion)
        end
    end
end

# TODO: Merge assertions if the program inbetween is emtpy


# - Clean up current branch
# - Make commits
# - delete unused code
# - Implement test cases
# - Implement goal printing
# - Integrate new graph generation into macro call
# - Implement the code that starts the KeYmaera X process
# - Implement the code that sends the proof goal to KeYmaera X
# - Implement the code that receives the proof result from KeYmaera X
# - Implement symbolic execution with proper error handling
# - Add for and while loops