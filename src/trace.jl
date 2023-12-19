using MacroTools, Test
# TODO: Clean up tests
# TODO: Add additional test cases
# TODO: Add error messages
# TODO: Translate dL_IR into a kyx file

function parse_function(ex)
    # TODO: Use the functions below to parse the expression into a dL_IR
    argument_variables = parse_arguments(ex)
    body_variables, program, assumptions, assertions = parse_body(ex)
    variables = union(argument_variables, body_variables)
    return dL_IR(variables, program, assumptions, assertions)
end

function parse_body(ex::Expr)
    ex = MacroTools.prewalk(rmlines, ex)
    assertions = collect_assertions(ex)
    assumptions = collect_assumptions(ex)
    variables = collect_unique_variables(ex)

    @capture(ex, (function f_(xs__) program_ end) | (f_(xs__) = program_))
    program = remove_assertions(program)
    program = remove_assumptions(program)

    return variables, program, assumptions, assertions
end


function collect_assumptions(ex::Expr)
    # TODO: Make sure that the assumptions are stated in the first line of the function
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    assumptions = Vector{Expr}()
    for x in body.args
        if isa(x, Expr) && @capture(x, @assume q_)
            push!(assumptions, q)
        end
    end
    return assumptions
end

function remove_assertions(body::Expr)
    return Expr(body.head, filter(x->!@capture(x, @assert q_), body.args)...)
end

function remove_assumptions(body::Expr)
    return Expr(body.head, filter(x->!@capture(x, @assume q_), body.args)...)
end

function collect_unique_variables(body::Expr)
    queue = [body]
    variables = Set{Tuple{Symbol, Symbol}}()
    while !isempty(queue)
        x = pop!(queue)
        #TODO: Check whether you need type inference
        if @capture(x, y_ = e_)
            push!(variables, (y, :Real))
        elseif isa(x, Expr)
            push!(queue, filter(z -> isa(z, Expr), x.args)...)
        end
    end

    return variables
end

struct dL_IR
    variables::Set{Tuple{Symbol, Symbol}}
    program::Expr
    assumptions::Vector{Expr}
    assertions::Vector{Expr}
end

function parse_arguments(ex)
    #TODO: Check whether this is robust
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))

    variables = Set{Tuple{Symbol, Symbol}}()
    for x in xs
        @capture(x, y_::t_)
        push!(variables, (y, t))
    end
    return variables
end



function collect_assertions(ex)
    # TODO: Make sure that the assertions are stated in the first line of the function
    # This does not work if assertions are nested in if statements
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    assertions = Vector{Expr}()
    for x in body.args
        if isa(x, Expr) && @capture(x, @assert q_)
            push!(assertions, q)
        end
    end
    return assertions
end

begin
    ex = quote
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

    ex_without_assertions = quote
        function max(x::Real, y::Real)
            @assume 0 <= x && 0 <= y
            if x >= y
                max_value = x
            else
                max_value = y
            end
            return max_value
        end
    end

    ex_without_assumptions = quote
        function max(x::Real, y::Real)
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
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    @capture(ex_without_assertions, (function f_(xs__) bodyassert_ end) | (f_(xs__) = bodyassert_))
    @capture(ex_without_assumptions, (function f_(xs__) bodyassume_ end) | (f_(xs__) = bodyassume_))

    @test collect_assumptions(ex) == [:(0 <= x && 0 <= y)]
    @test parse_arguments(ex) == Set{Tuple{Symbol, Symbol}}([(:x, :Real), (:y, :Real)])
    @test collect_assertions(ex) == [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]
    @test MacroTools.prewalk(rmlines, remove_assertions(body)) == MacroTools.prewalk(rmlines, bodyassert)
    @test MacroTools.prewalk(rmlines, remove_assumptions(body)) == MacroTools.prewalk(rmlines, bodyassume)
    @test collect_unique_variables(:()) == Set{Symbol}()
    @test collect_unique_variables(ex) == Set{Tuple{Symbol, Symbol}}([(:max_value, :Real)])


    variables = Set{Tuple{Symbol, Symbol}}([(:max_value, :Real)])
    program = quote
        if x >= y
            max_value = x
        else
            max_value = y
        end
        return max_value
    end
    program = MacroTools.prewalk(rmlines, program)
    assumptions = [:(0 <= x && 0 <= y)]
    assertions = [:(max_value >= x && max_value >= y), :(max_value == x || max_value == y)]
    result = parse_body(ex)
    @test result[1] == variables
    @test result[2] == program
    @test result[3] == assumptions
    @test result[4] == assertions

    variables = Set{Tuple{Symbol, Symbol}}([(:x, :Real), (:y, :Real), (:max_value, :Real)])
    result = parse_function(ex)
    @test result.variables == variables
    @test result.program == program
    @test result.assumptions == assumptions
    @test result.assertions == assertions
end