import Test
using Elenchos

variables = [(:x, :Real)]
@Test.test to_kyx_variable_string(variables) == ["Real x;"]

variables = [(:x, :Real), (:y, :Real)]
@Test.test to_kyx_variable_string(variables) == ["Real x;","Real y;"]

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

assumptions = []
assertions = []
program = Empty()
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "(true) -> [{}] (false)"


assumptions = [Equal(DlSymbol(:x), DlReal(1.0))]
assertions = []
program = Empty()
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "((x = 1.0)) -> [{}] (false)"

assumptions = [Equal(DlSymbol(:x), DlReal(1.0)), Equal(DlSymbol(:x), DlReal(1.0))]
assertions = []
program = Empty()
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "((x = 1.0) & (x = 1.0)) -> [{}] (false)"

assumptions = []
assertions = [Equal(DlSymbol(:x), DlReal(1.0))]
program = Empty()
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "(true) -> [{}] ((x = 1.0))"

assumptions = []
assertions = [Equal(DlSymbol(:x), DlReal(1.0)), Equal(DlSymbol(:x), DlReal(1.0))]
program = Empty()
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "(true) -> [{}] ((x = 1.0) & (x = 1.0))"

assumptions = []
assertions = []
program = Sequential(Assignment(DlSymbol(:x), DlReal(1.0)), Empty())
@Test.test to_kyx_problem_string(assumptions, assertions, program) == "(true) -> [{x := 1.0; }] (false)"

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

@Test.test to_kyx_file_string([], [], [], Empty()) == "ArchiveEntry \"test.kyx\"\n   ProgramVariables\n\n   End.\n   Problem\n      (true) -> [{}] (false)\n   End.\nEnd."


# Integration test

function_definition = quote
    function max(x::Real, y::Real)
        @assume 0 <= x && 0 <= y
        if x >= y
            max_value = x
        else
            max_value = y
        end
        
        @assert max_value >= x && max_value >= y
        @assert max_value == x || max_value == y
    end
end
# TODO: Rename to_kyx... functions to to_ir... functions
variables, program, assumptions, assertions = parse_function(function_definition)
program_ir = program_to_dl_ir(program)
assumptions_ir = map(x -> formula_to_dl_ir(x), assumptions)
assertions_ir = map(x -> formula_to_dl_ir(x), assertions)
print(to_kyx_file_string(variables, assumptions_ir, assertions_ir, program_ir))

macro elenchos(function_definition)
    variables, program, assumptions, assertions = parse_function(function_definition)
    program_ir = program_to_dl_ir(program)
    assumptions_ir = map(x -> formula_to_dl_ir(x), assumptions)
    assertions_ir = map(x -> formula_to_dl_ir(x), assertions)
    return to_kyx_file_string(variables, assumptions_ir, assertions_ir, program_ir)
end

kyx_string = @elenchos function max(x::Real, y::Real)
    @assume 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
end

println(kyx_string)