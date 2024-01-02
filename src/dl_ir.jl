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

@enum FormulaSymbol less_or_equal greater_or_equal less greater equal not_equal and or not bool_true bool_false
"""
    Formula
    Syntax: e, q, E, Q := e <= q, e < q, e = q, e > q, e >= q, e != q, E && Q, E || Q, !E
"""
struct Formula
    symbol::FormulaSymbol
    # Has either zero, one or two subformulas
    first_subformula::Union{Formula, Nothing}
    second_subformula::Union{Formula, Nothing}
    # Has either zero, one or two subexpressions
    first_expressions::Union{Expression, Nothing}
    second_expressions::Union{Expression, Nothing}
end

Not(formula::Formula) = Formula(not, formula, nothing, nothing, nothing)
And(formula1::Formula, formula2::Formula) = Formula(and, formula1, formula2, nothing, nothing)
Or(formula1::Formula, formula2::Formula) = Formula(or, formula1, formula2, nothing, nothing)
LessOrEqual(expression1::Expression, expression2::Expression) = Formula(less_or_equal, nothing, nothing, expression1, expression2)
GreaterOrEqual(expression1::Expression, expression2::Expression) = Formula(greater_or_equal, nothing, nothing, expression1, expression2)
Less(expression1::Expression, expression2::Expression) = Formula(less, nothing, nothing, expression1, expression2)
Greater(expression1::Expression, expression2::Expression) = Formula(greater, nothing, nothing, expression1, expression2)
Equal(expression1::Expression, expression2::Expression) = Formula(equal, nothing, nothing, expression1, expression2)
NotEqual(expression1::Expression, expression2::Expression) = Formula(not_equal, nothing, nothing, expression1, expression2)
BoolTrue() = Formula(bool_true, nothing, nothing, nothing, nothing)
BoolFalse() = Formula(bool_false, nothing, nothing, nothing, nothing)

#TODO: Allow for the usage of true and false
function formula_to_kyx(formula)
    symbol_to_formula = Dict(
        :<= => less_or_equal,
        :>= => greater_or_equal,
        :< => less,
        :> => greater,
        :(==) => equal,
        :!= => not_equal,
        :&& => and,
        :|| => or,
        :! => not,
    )
    if isa(formula, Bool)
        if formula
            value = bool_true
        else
            value = bool_false
        end
        kyx_formula = Formula(value, nothing, nothing, nothing, nothing)
    elseif formula.head in [:&&, :||]
        kyx_formula = Formula(symbol_to_formula[formula.head], formula_to_kyx(formula.args[1]), formula_to_kyx(formula.args[2]), nothing, nothing)
    elseif formula.head == :call
        symbol = formula.args[1]
        
        if symbol in [:<=, :>=, :<, :>, :(==), :!=]
            kyx_formula = Formula(symbol_to_formula[symbol], nothing, nothing, expression_to_kyx(formula.args[2]), expression_to_kyx(formula.args[3]))
        elseif symbol == :!
            kyx_formula = Formula(symbol_to_formula[symbol], formula_to_kyx(formula.args[2]), nothing, nothing, nothing)
        end
    end
    return kyx_formula

end

export ExpressionSymbol, plus, minus, mult, div, real, symbol
export FormulaSymbol, less_or_equal, greater_or_equal, less, greater, equal, not_equal, and, or, not, bool_true, bool_false
export expression_to_kyx, formula_to_kyx, Expression, Formula
export Not, And, Or, LessOrEqual, GreaterOrEqual, Less, Greater, Equal, NotEqual, BoolTrue, BoolFalse