import Test
using MacroTools, Elenchos

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
        return max_value
    end
end
function_definition = MacroTools.prewalk(rmlines, function_definition)

body = quote
    @assume 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
    return max_value
end

body = MacroTools.prewalk(rmlines, body)

body_without_assertions = quote
    @assume 0 <= x && 0 <= y
    if x >= y
        max_value = x
    else
        max_value = y
    end
    return max_value
end
body_without_assertions = MacroTools.prewalk(rmlines, body_without_assertions)

body_without_assumption = quote
    if x >= y
        max_value = x
    else
        max_value = y
    end
    
    @assert max_value >= x && max_value >= y
    @assert max_value == x || max_value == y
    return max_value
end
body_without_assumption = MacroTools.prewalk(rmlines, body_without_assumption)

body_wihout_assumptions_and_assertions = quote
    if x >= y
        max_value = x
    else
        max_value = y
    end
    return max_value
end
body_wihout_assumptions_and_assertions = MacroTools.prewalk(rmlines, body_wihout_assumptions_and_assertions)


assumptions  = [:(0 <= x && 0 <= y)]
assertions = [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]
body_variables = Set{Tuple{Symbol, Symbol}}([(:max_value, :Real)])
argument_variables = Set{Tuple{Symbol, Symbol}}([(:x, :Real), (:y, :Real)])



@Test.test collect_assumptions(function_definition) == assumptions
@Test.test parse_arguments(function_definition) == argument_variables
@Test.test collect_assertions(function_definition) == assertions
@Test.test remove_assertions(body) == body_without_assertions
@Test.test remove_assumptions(body) == body_without_assumption
@Test.test collect_unique_variables(function_definition) == body_variables


result = parse_body(function_definition)
@Test.test result[1] == body_variables
@Test.test result[2] == body_wihout_assumptions_and_assertions
@Test.test result[3] == assumptions
@Test.test result[4] == assertions

program_variables = union(argument_variables, body_variables)
result = parse_function(function_definition)
@Test.test result.variables == program_variables
@Test.test result.program == body_wihout_assumptions_and_assertions
@Test.test result.assumptions == assumptions
@Test.test result.assertions == assertions



empty_function = quote
    function f()
    end
end

body = quote
end
body = MacroTools.prewalk(rmlines, body)

assumptions  = []
argument_variables = Set{Tuple{Symbol, Symbol}}()
assertions = []
body_variables = Set{Tuple{Symbol, Symbol}}()
body_without_assertions = body
body_without_assumption = body
body_wihout_assumptions_and_assertions = body



@Test.test collect_assumptions(empty_function) == assumptions
@Test.test parse_arguments(empty_function) == argument_variables
@Test.test collect_assertions(empty_function) == assertions
@Test.test collect_unique_variables(empty_function) == body_variables
@Test.test remove_assertions(body) == body_without_assertions
@Test.test remove_assumptions(body) == body_without_assumption


result = parse_body(empty_function)
@Test.test result[1] == body_variables
@Test.test result[2] == body_wihout_assumptions_and_assertions
@Test.test result[3] == assumptions
@Test.test result[4] == assertions

program_variables = union(argument_variables, body_variables)
result = parse_function(empty_function)
@Test.test result.variables == program_variables
@Test.test result.program == body_wihout_assumptions_and_assertions
@Test.test result.assumptions == assumptions
@Test.test result.assertions == assertions

begin
    program = Base.remove_linenums!(
        quote
        end
    )
    @Test.test program_to_kyx(program) == Empty()

    program = Base.remove_linenums!(
        quote
            x = 1
        end
    )
    @Test.test program_to_kyx(program) == Sequential(Assignment(DlSymbol(:x), DlReal(1)), Empty())
    
    program = :(x = 1)
    @Test.test program_to_kyx(program) == Assignment(DlSymbol(:x), DlReal(1))

    program = Base.remove_linenums!(:( if true else end))
    @Test.test program_to_kyx(program) == Choice(
        Sequential(
            DlTest(BoolTrue()),
            Empty()),
        Sequential(
            DlTest(Not(BoolTrue())),
            Empty()
        )
    )
end
begin
    formula = :(true)
    @Test.test formula_to_kyx(formula) == BoolTrue()

    formula = :(false)
    @Test.test formula_to_kyx(formula) == BoolFalse()

    formula = :(0.0 <= x)
    @Test.test formula_to_kyx(formula) == LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 < x)
    @Test.test formula_to_kyx(formula) == Less(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 >= x)
    @Test.test formula_to_kyx(formula) == GreaterOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 > x)
    @Test.test formula_to_kyx(formula) == Greater(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 == x)
    @Test.test formula_to_kyx(formula) == Equal(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 != x)
    @Test.test formula_to_kyx(formula) == NotEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 <= x && x <= 1.0)
    @Test.test formula_to_kyx(formula) == And(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(0.0 <= x || x <= 1.0)
    @Test.test formula_to_kyx(formula) == Or(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(!(0.0 <= x))
    @Test.test formula_to_kyx(formula) == Not(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)))
end

begin
    expression = :(1.0 + 1.2)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 + (1.2 + 1.3)) 
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(plus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 + 1.2) + 1.3)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    epression = :(1.0 + 1.2 + 1.3)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 - 1.2)
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 - (1.2 - 1.3))
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(minus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 - 1.2) - 1.3)
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 * (1.2 * 1.3))
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 * 1.2) * 1.3)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2 * 1.3)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 / 1.2)
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 / (1.2 / 1.3))
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.div, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 / 1.2) / 1.3)
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))
    
    expression = :(1.0 + 1.2 * 1.3 )
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :(1.0 * 1.2 + 1.3 )
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(x)
    @Test.test expression_to_kyx(expression) == Expression(symbol, :x, nothing)
end