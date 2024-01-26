import Test
using Elenchos: to_kyx_variable_string, to_kyx_problem_string, to_kyx_file_string

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


