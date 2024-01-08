export @elenchos

using MacroTools

function parse_function(ex)
    argument_variables = parse_arguments(ex)
    body_variables, program, assumptions, assertions = parse_body(ex)
    variables = union(argument_variables, body_variables)
    return variables, program, assumptions, assertions
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
    # TODO: Make this work if assumptions are nested in if statements or loops
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
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    # TODO: Make sure that the assertions are stated in the first line of the function
    # This does not work if assertions are nested in if statements
    last_is_true = false
    assertions = [[]]
    for x in body.args
        if isa(x, Expr) && @capture(x, @assert q_) && !last_is_true
            push!(assertions, [q])
            last_is_true = true
        elseif isa(x, Expr) && @capture(x, @assert q_) && last_is_true
            push!(assertions[end], q)
        else
            last_is_true = false
        end
    end
    return assertions
end

function collect_programs(ex) 
    @capture(ex, (function f_(xs__) body_ end) | (f_(xs__) = body_))
    last_is_true = false
    programs = [[]]
    for x in body.args
        if isa(x, Expr) && @capture(x, @assert q_) && !last_is_true
            push!(programs, [])
            last_is_true = true
        elseif !(isa(x, Expr) && @capture(x, @assert q_))
            push!(programs[end], x)
            last_is_true = false
        end
    end
    return programs
end


include("to_kyx_string.jl")

macro elenchos(function_definition)
    variables, program, assumptions, assertions = parse_function(function_definition)
    program_ir = program_to_dl_ir(program)
    assumptions_ir = map(x -> formula_to_dl_ir(x), assumptions)
    assertions_ir = map(x -> formula_to_dl_ir(x), assertions)
    return to_kyx_file_string(variables, assumptions_ir, assertions_ir, program_ir)
end