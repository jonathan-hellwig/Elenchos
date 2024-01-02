@enum ExpressionSymbol plus minus mult div real symbol

struct Expression
    symbol::ExpressionSymbol
    left::Union{Expression, Symbol, Real}
    right::Union{Expression, Nothing}
end

function expression_to_kyx(expression)
    if isa(expression, Real)
        return Expression(real, expression, nothing)
    elseif isa(expression, Symbol)
        return Expression(symbol, expression, nothing)
    end
    if expression.head != :call
        error("Not a call expression!")
    end

    expression_symbol = expression.args[1]
    if expression_symbol == :+
        kyx_expression = Expression(plus, expression_to_kyx(expression.args[2]), expression_to_kyx(expression.args[3]))
        for i in 4:length(expression.args)
            kyx_expression = Expression(plus, kyx_expression, expression_to_kyx(expression.args[i]))
        end
    elseif expression_symbol == :-
        kyx_expression = Expression(minus, expression_to_kyx(expression.args[2]), expression_to_kyx(expression.args[3]))
    elseif expression_symbol == :*
        kyx_expression = Expression(mult, expression_to_kyx(expression.args[2]), expression_to_kyx(expression.args[3]))
        for i in 4:length(expression.args)
            kyx_expression = Expression(mult, kyx_expression, expression_to_kyx(expression.args[i]))
        end
    elseif expression_symbol == :/
        kyx_expression = Expression(div, expression_to_kyx(expression.args[2]), expression_to_kyx(expression.args[3]))
    else
        error("Unknown operator!")
    end
    return kyx_expression
end