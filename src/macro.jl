export @elenchos

using MacroTools

function parse_function(ex)
    ex = MacroTools.prewalk(rmlines, ex)
    @capture(ex, (function f_(xs__)
        body_
    end) | (f_(xs__) = body_))
    argument_variables = parse_arguments(xs)
    body_variables, programs, assertions = parse_body(body)
    variables = union(argument_variables, body_variables)
    return variables, programs, assertions
end

function parse_body(function_body::Expr)
    function_body = MacroTools.prewalk(rmlines, function_body)
    assertions = collect_assertions(function_body)
    variables = collect_unique_variables(function_body)
    programs = collect_programs(function_body)

    return variables, programs, assertions
end

function collect_unique_variables(body::Expr)
    queue = [body]
    variables = Set{Tuple{Symbol,Symbol}}()
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

function parse_arguments(arguments)
    #TODO: Check whether this is robust
    variables = Set{Tuple{Symbol,Symbol}}()
    for x in arguments
        @capture(x, y_::t_)
        push!(variables, (y, t))
    end
    return variables
end

function collect_assertions(function_body)
    if isempty(function_body.args)
        return [[:(true)], [:(true)]]
    end
    # This does not work if assertions are nested in if statements
    program_not_empty = false
    last_is_assert = false
    assertions = []

    for x in function_body.args
        is_assert = isa(x, Expr) && @capture(x, @assert q_)
        if is_assert && !last_is_assert
            push!(assertions, Vector{Union{Expr,Bool}}([q]))
            last_is_assert = true
        elseif is_assert && last_is_assert
            push!(assertions[end], q)
        else
            last_is_assert = false
            program_not_empty = true
        end
    end
    # TODO: Fix the case where the program is empty
    is_assert = isa(function_body.args[1], Expr) && @capture(function_body.args[1], @assert q_)
    if is_assert && last_is_assert && !program_not_empty
        pushfirst!(assertions, [:(true)])
    else
        if !last_is_assert
            push!(assertions, [:(true)])
        end
        if !is_assert
            pushfirst!(assertions, [:(true)])
        end
    end
    return assertions
end

function collect_lines(function_body)
    programs = [[]]
    has_assertions = false
    last_is_assert = false
    for x in function_body.args
        if isa(x, Expr) && @capture(x, @assert q_)
            last_is_assert = true
        else
            if has_assertions && last_is_assert
                push!(programs, [x])
            else
                has_assertions = true
                push!(programs[end], x)
            end
            last_is_assert = false
        end
    end

    return programs
end

function collect_programs(function_body)
    programs = []
    for program in collect_lines(function_body)
        push!(programs, Expr(:block, program...))
    end
    return programs
end

function propagate_formulas(formulas, programs)
    formulas = deepcopy(formulas)
    for (current_formulas, next_formulas, program) in zip(formulas[1:end-1], formulas[2:end], programs)
        modified_variables = get_modified_variables(program)
        for formula in current_formulas
            free_variables = get_variables(formula)
            if isempty(intersect(free_variables, modified_variables))
                push!(next_formulas, formula)
            end
        end
    end
    return formulas
end

include("to_kyx_string.jl")

macro elenchos(function_definition)
    variables, programs, assertions = parse_function(function_definition)
    programs_ir = map(x -> program_to_dl_ir(x), programs)
    assertions_ir = [map(x -> formula_to_dl_ir(x), assertion) for assertion in assertions]
    propagated_assertions_ir = propagate_formulas(assertions_ir, programs_ir)

    for (program, assumptions, assertions) in zip(programs_ir, propagated_assertions_ir[1:end-1], propagated_assertions_ir[2:end])
        println(to_kyx_file_string(variables, assumptions, assertions, program))
    end
end