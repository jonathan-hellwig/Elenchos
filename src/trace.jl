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

export parse_function, parse_body, collect_assumptions, remove_assertions, remove_assumptions, collect_unique_variables, dL_IR, parse_arguments, collect_assertions