import Test
using Elenchos

@Test.testset "Test to_kyx_variable_string" begin
    variables = [(:x, :Real)]
    @Test.test to_kyx_variable_string(variables) == ["Real x;"]

    variables = [(:x, :Real), (:y, :Real)]
    @Test.test to_kyx_variable_string(variables) == ["Real x;","Real y;"]
end

@Test.testset "Test to_kyx_problem_string" begin
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
end

@Test.testset "Test to_kyx_file_string" begin
    @Test.test to_kyx_file_string([], [], [], Empty()) == "ArchiveEntry \"test.kyx\"\n   ProgramVariables\n\n   End.\n   Problem\n      (true) -> [{}] (false)\n   End.\nEnd."
end


# # Integration test

# function_definition = quote
#     function max(x::Real, y::Real)
#         @assume 0 <= x && 0 <= y
#         if x >= y
#             max_value = x
#         else
#             max_value = y
#         end
        
#         @assert max_value >= x && max_value >= y
#         @assert max_value == x || max_value == y
#     end
# end


