import Test
using MacroTools
using Elenchos: parse_arguments, collect_assertions, collect_programs, collect_unique_variables, parse_body, parse_function, collect_lines, propagate_formulas
import Elenchos
Test.@testset "Test macro" begin
    function_definition = quote
        function max(x::Real, y::Real)
            @assert 0 <= x && 0 <= y
            if x >= y
                max_value = x
            else
                max_value = y
            end

            @assert max_value >= x && max_value >= y
            @assert max_value == x || max_value == y
        end
    end
    function_definition = MacroTools.prewalk(rmlines, function_definition)
    arguments = [:(x::Real), :(y::Real)]
    body = quote
        @assert 0 <= x && 0 <= y
        if x >= y
            max_value = x
        else
            max_value = y
        end

        @assert max_value >= x && max_value >= y
        @assert max_value == x || max_value == y
    end

    body = MacroTools.prewalk(rmlines, body)

    assertions = [[:(0 <= x && 0 <= y)], [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]]
    body_variables = Set{Tuple{Symbol,Symbol}}([(:max_value, :Real)])
    argument_variables = Set{Tuple{Symbol,Symbol}}([(:x, :Real), (:y, :Real)])

    Test.@test parse_arguments(arguments) == argument_variables
    Test.@test collect_assertions(body) == assertions
    Test.@test collect_unique_variables(body) == body_variables


    empty_function = quote
        function f()
        end
    end
    arguments = []
    body = quote end
    body = MacroTools.prewalk(rmlines, body)

    assumptions = []
    argument_variables = Set{Tuple{Symbol,Symbol}}()
    assertions = [[:(true)], [:(true)]]
    body_variables = Set{Tuple{Symbol,Symbol}}()

    Test.@test parse_arguments(arguments) == argument_variables
    Test.@test collect_assertions(body) == assertions
    Test.@test collect_unique_variables(body) == body_variables

    function_definition = Base.remove_linenums!(quote
        function max(x::Real, y::Real)
            @assert 0 <= x && 0 <= y
            if x >= y
                max_value = x
            else
                max_value = y
            end
            @assert max_value >= x && max_value >= y
            @assert max_value == x || max_value == y
        end
    end)

    variables, programs, assertions = parse_function(function_definition)

    Test.@test variables == Set{Tuple{Symbol,Symbol}}([(:max_value, :Real), (:x, :Real), (:y, :Real)])
    # TODO: programs consists of two elements, but it should be one
    Test.@test programs == [Base.remove_linenums!(quote
        if x >= y
            max_value = x
        else
            max_value = y
        end
    end)]
    Test.@test assertions == [[:(0 <= x && 0 <= y)], [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]]
end

Test.@testset "Test collect_assertions and collect_programs" begin
    function_body = Base.remove_linenums!(quote
        @assert true
        @assert x == 2
        x = 1
        @assert x == 2
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[true, :(x == 2)], [:(x == 2), :(x == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert true
        x = 1
        @assert x == 2
    end)

    Test.@test collect_assertions(function_body) == [[:(true)], [:(x == 2)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert true
        @assert x == 2
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[:(true)], [:(true), :(x == 2), :(x == 1)]]
    Test.@test collect_lines(function_body) == [[]]

    function_body = Base.remove_linenums!(quote
        x = 1
        x = 2
        x = 3
    end)

    Test.@test collect_assertions(function_body) == [[:(true)], [:(true)]]
    Test.@test collect_lines(function_body) == [[:(x = 1), :(x = 2), :(x = 3)]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
        x = 1
    end)
    Test.@test collect_assertions(function_body) == [[:(y == 1)], [:(true)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        x = 1
        @assert y == 1
    end)
    Test.@test collect_assertions(function_body) == [[:(true)], [:(y == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]


    function_body = Base.remove_linenums!(quote
        x = 1
    end)
    Test.@test collect_assertions(function_body) == [[:(true)], [:(true)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
        x = 1
        @assert y == 1
    end)
    Test.@test collect_assertions(function_body) == [[:(y == 1)], [:(y == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
    end)
    Test.@test collect_assertions(function_body) == [[:(true)], [:(y == 1)]]
    Test.@test collect_lines(function_body) == [[]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[:(true)], [:(y == 1), :(x == 1)]]
    Test.@test collect_lines(function_body) == [[]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
        x = 1
        @assert y == 1
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[:(y == 1)], [:(y == 1), :(x == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert y == 1
        x = 1
        @assert y == 1
        x = 1
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[:(y == 1)], [:(y == 1)], [:(x == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)], [:(x = 1)]]

    function_body = Base.remove_linenums!(quote
        @assert x == 1
        @assert y == 1
        x = 1
        @assert y == 1
        x = 1
        @assert x == 1
    end)

    Test.@test collect_assertions(function_body) == [[:(x == 1), :(y == 1)], [:(y == 1)], [:(x == 1)]]
    Test.@test collect_lines(function_body) == [[:(x = 1)], [:(x = 1)]]

end

Test.@testset "Test propagate_formulas" begin
    formulas = [[]]
    programs = []
    Test.@test formulas == [[]]

    formulas = [[], [Equal(DlSymbol(:x), DlReal(1))], []]
    programs = [Empty(), Empty(), Empty()]

    Test.@test propagate_formulas(formulas, programs) == [[], [Equal(DlSymbol(:x), DlReal(1))], [Equal(DlSymbol(:x), DlReal(1))]]

    formulas = [[], [Equal(DlSymbol(:x), DlReal(1))], []]
    programs = [Empty(), Assignment(DlSymbol(:x), DlReal(1)), Empty()]

    Test.@test propagate_formulas(formulas, programs) == [[], [Equal(DlSymbol(:x), DlReal(1))], []]
end

using Elenchos
provables = @elenchos function max(x::Real, y::Real)
    @assert x > 0
    if x > y
        max_value = x
    else
        max_value = y
    end
    @assert max_value >= x
end

print(provables[1])
print(provables[2])