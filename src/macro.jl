export @elenchos

using MacroTools


function parse_function(ex)
    # ex = MacroTools.prewalk(rmlines, ex)
    @capture(ex, (function f_(xs__)
        body_
    end) | (f_(xs__) = body_))
    body = Expr(:block, body.args[2:end]...)
    argument_variables = parse_arguments(xs)
    body_variables = collect_unique_variables(body)
    variables = union(argument_variables, body_variables)

    graphs = build_graph(body)
    assertions = get_assertions(body)

    return variables, graphs, assertions
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

include("to_kyx_string.jl")
include("proof_goal.jl")
macro elenchos(function_definition)
    variables, graphs, assertions = parse_function(function_definition)
    provables = []
    for graph in graphs
        for (goal, parent) in graph
            if !isnothing(parent) && !isnothing(goal.assertion_line) && !isempty(goal.program)
                program = program_to_dl_ir(Expr(:block, goal.program...))
                assumptions_ir = map(x -> formula_to_dl_ir(x), assertions[parent.assertion_line])
                assertions_ir = map(x -> formula_to_dl_ir(x), assertions[goal.assertion_line])
                push!(provables, to_kyx_file_string(variables, assumptions_ir, assertions_ir, program))
            end
        end
    end
    return provables
end

