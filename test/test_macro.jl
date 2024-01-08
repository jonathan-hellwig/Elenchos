import Test
using MacroTools
using Elenchos: remove_assertions, remove_assumptions, collect_assumptions, parse_arguments, collect_assertions, collect_programs, collect_unique_variables, parse_body, parse_function
import Elenchos
Test.@testset "Test macro" begin
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
    arguments = [:(x::Real), :(y::Real)]
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


    assumptions = [:(0 <= x && 0 <= y)]
    assertions = [[], [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]]
    body_variables = Set{Tuple{Symbol,Symbol}}([(:max_value, :Real)])
    argument_variables = Set{Tuple{Symbol,Symbol}}([(:x, :Real), (:y, :Real)])



    Test.@test collect_assumptions(body) == assumptions
    Test.@test parse_arguments(arguments) == argument_variables
    Test.@test collect_assertions(body) == assertions
    Test.@test remove_assertions(body) == body_without_assertions
    Test.@test remove_assumptions(body) == body_without_assumption
    Test.@test collect_unique_variables(body) == body_variables


    result = parse_body(body)
    Test.@test result[1] == body_variables
    Test.@test result[2] == body_wihout_assumptions_and_assertions
    Test.@test result[3] == assumptions
    Test.@test result[4] == assertions

    program_variables = union(argument_variables, body_variables)
    result = parse_function(function_definition)
    Test.@test result[1] == program_variables
    Test.@test result[2] == body_wihout_assumptions_and_assertions
    Test.@test result[3] == assumptions
    Test.@test result[4] == assertions



    empty_function = quote
        function f()
        end
    end
    arguments = []
    body = quote end
    body = MacroTools.prewalk(rmlines, body)

    assumptions = []
    argument_variables = Set{Tuple{Symbol,Symbol}}()
    assertions = [[]]
    body_variables = Set{Tuple{Symbol,Symbol}}()
    body_without_assertions = body
    body_without_assumption = body
    body_wihout_assumptions_and_assertions = body



    Test.@test collect_assumptions(body) == assumptions
    Test.@test parse_arguments(arguments) == argument_variables
    Test.@test collect_assertions(body) == assertions
    Test.@test collect_unique_variables(body) == body_variables
    Test.@test remove_assertions(body) == body_without_assertions
    Test.@test remove_assumptions(body) == body_without_assumption


    result = parse_body(body)
    Test.@test result[1] == body_variables
    Test.@test result[2] == body_wihout_assumptions_and_assertions
    Test.@test result[3] == assumptions
    Test.@test result[4] == assertions

    program_variables = union(argument_variables, body_variables)
    result = parse_function(empty_function)
    Test.@test result[1] == program_variables
    Test.@test result[2] == body_wihout_assumptions_and_assertions
    Test.@test result[3] == assumptions
    Test.@test result[4] == assertions
end

Test.@testset "Test collect_assertions and collect_programs" begin
    function_body = Base.remove_linenums!(quote
            @assert true
            @assert x == 2
            x = 1
            @assert x == 2
            @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[], [true, :(x == 2)], [:(x == 2), :(x == 1)]]
    Test.@test collect_programs(function_body) == [[], [:(x = 1)], []]

    function_body = Base.remove_linenums!(quote
            @assert true
            x = 1
            @assert x == 2
    end)

    Test.@test collect_assertions(function_body) == [[], [true], [:(x == 2)]]
    Test.@test collect_programs(function_body) == [[], [:(x = 1)], []]

    function_body = Base.remove_linenums!(quote
            @assert true
            @assert x == 2
            @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[], [true, :(x == 2), :(x == 1)]]
    Test.@test collect_programs(function_body) == [[], []]

    function_body = Base.remove_linenums!(quote
            x = 1
            x = 2
            x = 3
    end)

    Test.@test collect_assertions(function_body) == [[]]
    Test.@test collect_programs(function_body) == [[:(x = 1), :(x = 2), :(x = 3)]]
end