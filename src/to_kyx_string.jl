include("dl_ir_to_string.jl")
include("utils.jl")
function to_kyx_variable_string(variables)
    if isempty(variables)
        return ""
    end
    variables = collect(variables)
    variables_strings = map(x -> "Real "*snake_case_to_camel_case(string(x[1]))*";", variables)
    return variables_strings
end

function to_kyx_problem_string(assumptions, assertions, program)
    if isempty(assumptions)
        assumptions_string = "true"
    else
        assumptions_string = map(x -> "(" * formula_to_string(x) * ")", assumptions)
        assumptions_string = join(assumptions_string, " & ")
    end

    if isempty(assertions)
        assertions_string = "false"
    else
        assertions_string = map(x -> "(" * formula_to_string(x) * ")", assertions)
        assertions_string = join(assertions_string, " & ")
    end

    return "(" * assumptions_string * ")" * " -> [{"* program_to_string(program) *"}] " * "(" * assertions_string * ")"
end

function to_kyx_file_string(variables, assumptions, assertions, program)
    variables_strings = to_kyx_variable_string(variables)
    variables_strings = map(x -> "      "*x, variables_strings)
    variables_string = join(variables_strings, "\n")
    problem_string = to_kyx_problem_string(assumptions, assertions, program)

    kyx_string = "ArchiveEntry \"test.kyx\"\n" *
                    "   ProgramVariables\n" *
                        variables_string * "\n" *
                    "   End.\n" *
                    "   Problem\n" *
                    "      " * problem_string * "\n" *
                    "   End.\n" *
                    "End."
    return kyx_string
end