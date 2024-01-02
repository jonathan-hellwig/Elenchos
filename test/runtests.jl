using Test, MacroTools, Elenchos

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



@test collect_assumptions(function_definition) == assumptions
@test parse_arguments(function_definition) == argument_variables
@test collect_assertions(function_definition) == assertions
@test remove_assertions(body) == body_without_assertions
@test remove_assumptions(body) == body_without_assumption
@test collect_unique_variables(function_definition) == body_variables


result = parse_body(function_definition)
@test result[1] == body_variables
@test result[2] == body_wihout_assumptions_and_assertions
@test result[3] == assumptions
@test result[4] == assertions

program_variables = union(argument_variables, body_variables)
result = parse_function(function_definition)
@test result.variables == program_variables
@test result.program == body_wihout_assumptions_and_assertions
@test result.assumptions == assumptions
@test result.assertions == assertions



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



@test collect_assumptions(empty_function) == assumptions
@test parse_arguments(empty_function) == argument_variables
@test collect_assertions(empty_function) == assertions
@test collect_unique_variables(empty_function) == body_variables
@test remove_assertions(body) == body_without_assertions
@test remove_assumptions(body) == body_without_assumption


result = parse_body(empty_function)
@test result[1] == body_variables
@test result[2] == body_wihout_assumptions_and_assertions
@test result[3] == assumptions
@test result[4] == assertions

program_variables = union(argument_variables, body_variables)
result = parse_function(empty_function)
@test result.variables == program_variables
@test result.program == body_wihout_assumptions_and_assertions
@test result.assumptions == assumptions
@test result.assertions == assertions


begin
    expression = :(1.0 + 1.2)
    @test expression_to_kyx(expression) == Expression(plus, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing))

    expression = :(1.0 + (1.2 + 1.3)) 
    @test expression_to_kyx(expression) == Expression(plus, Expression(real, 1.0, nothing), Expression(plus, Expression(real, 1.2, nothing), Expression(real, 1.3, nothing)))

    expression = :((1.0 + 1.2) + 1.3)
    @test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    epression = :(1.0 + 1.2 + 1.3)
    @test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    expression = :(1.0 - 1.2)
    @test expression_to_kyx(expression) == Expression(minus, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing))

    expression = :(1.0 - (1.2 - 1.3))
    @test expression_to_kyx(expression) == Expression(minus, Expression(real, 1.0, nothing), Expression(minus, Expression(real, 1.2, nothing), Expression(real, 1.3, nothing)))

    expression = :((1.0 - 1.2) - 1.3)
    @test expression_to_kyx(expression) == Expression(minus, Expression(minus, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    expression = :(1.0 * 1.2)
    @test expression_to_kyx(expression) == Expression(mult, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing))

    expression = :(1.0 * (1.2 * 1.3))
    @test expression_to_kyx(expression) == Expression(mult, Expression(real, 1.0, nothing), Expression(mult, Expression(real, 1.2, nothing), Expression(real, 1.3, nothing)))

    expression = :((1.0 * 1.2) * 1.3)
    @test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    expression = :(1.0 * 1.2 * 1.3)
    @test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    expression = :(1.0 / 1.2)
    @test expression_to_kyx(expression) == Expression(div, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing))

    expression = :(1.0 / (1.2 / 1.3))
    @test expression_to_kyx(expression) == Expression(div, Expression(real, 1.0, nothing), Expression(div, Expression(real, 1.2, nothing), Expression(real, 1.3, nothing)))

    expression = :((1.0 / 1.2) / 1.3)
    @test expression_to_kyx(expression) == Expression(div, Expression(div, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))
    
    expression = :(1.0 + 1.2 * 1.3 )
    @test expression_to_kyx(expression) == Expression(plus, Expression(real, 1.0, nothing), Expression(mult, Expression(real, 1.2, nothing), Expression(real, 1.3, nothing)))

    expression = :(1.0 * 1.2 + 1.3 )
    @test expression_to_kyx(expression) == Expression(plus, Expression(mult, Expression(real, 1.0, nothing), Expression(real, 1.2, nothing)), Expression(real, 1.3, nothing))

    expression = :(x)
    @test expression_to_kyx(expression) == Expression(symbol, :x, nothing)
end