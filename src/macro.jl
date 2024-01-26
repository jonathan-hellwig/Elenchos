export @elenchos

using MacroTools
using HTTP


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
    for graph in graphs
        propagate_modified(graph)
    end
    for graph in graphs
        propagate_assertions(graph)
    end

    return variables, graphs
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

function parse_response(response)
    if isnothing(response)
        return nothing
    end
    body = String(response.body)
    if contains(body, "PROVED")
        return true
    elseif contains(body, "UNFINISHED")
        return false
    else
        return nothing
    end
end

macro elenchos(function_definition)
    variables, graphs = parse_function(function_definition)
    provables = Iterators.flatmap(x -> proof_obligations(x), graphs)

    is_success = true
    for provable in provables
        name = hash(provable)
        assumptions, assertions, program = provable
        assumptions_ir = map(x -> formula_to_dl_ir(x), collect(assumptions))
        assertions_ir = map(x -> formula_to_dl_ir(x), collect(assertions))
        program = program_to_dl_ir(program)

        kyx_string = to_kyx_file_string(variables, assumptions_ir, assertions_ir, program, name)
        response = nothing
        try
            response = HTTP.post("http://localhost:8070/check", Dict("Content-Type" => "text/plain"), kyx_string)
        catch 
            println("Failed to send proof request")
            is_success = false
            break
        end
        is_success = parse_response(response)
        if isnothing(is_success)
            println("Unexpected error")
            break
        end
        if is_success
            println("Proved ", to_kyx_problem_string(assumptions_ir, assertions_ir, program))
        else
            println("Failed to prove ", to_kyx_problem_string(assumptions_ir, assertions_ir, program))
            break
        end
    end
    if is_success
        println("Proved all provables")
    else
        println("Failed to prove all provables")
    end
end
