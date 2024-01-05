@enum ExpressionSymbol plus minus mult div real symbol

struct Expression
    symbol::ExpressionSymbol
    left::Union{Expression,Symbol,Real}
    right::Union{Expression,Nothing}
end
Plus(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(plus, left, right)
Minus(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(minus, left, right)
Mult(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(mult, left, right)
Div(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(div, left, right)
DlReal(value::Real) = Expression(real, value, nothing)
DlSymbol(dlsymbol::Symbol) = Expression(symbol, dlsymbol, nothing)

@enum FormulaSymbol less_or_equal greater_or_equal less greater equal not_equal and or not bool_true bool_false
"""
    Formula
    Syntax: e, q, E, Q := e <= q, e < q, e = q, e > q, e >= q, e != q, E && Q, E || Q, !E
"""
struct Formula
    symbol::FormulaSymbol
    # Has either zero, one or two subformulas
    first_subformula::Union{Formula,Nothing}
    second_subformula::Union{Formula,Nothing}
    # Has either zero, one or two subexpressions
    first_expressions::Union{Expression,Nothing}
    second_expressions::Union{Expression,Nothing}
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

@enum ProgramSymbol assign choice sequential dl_test empty

"""
    Program
    A program is a sequence of assignments, choices and tests.
    Syntax: α, β, Q, x, e ::= α;β | ?Q | α ∪ β | x := e
"""
struct Program
    #TODO: Introduce partial constructors
    symbol::ProgramSymbol
    first_programs::Union{Program,Nothing}
    second_programs::Union{Program,Nothing}
    formula::Union{Formula,Nothing}
    expressions::Union{Tuple{Expression,Expression},Nothing}
end
#TODO: Add a custom constructor for each symbol
Assignment(symbol::Expression, expression::Expression) = Program(assign, nothing, nothing, nothing, (symbol, expression))
Choice(first_program::Program, second_program::Program) = Program(choice, first_program, second_program, nothing, nothing)
Sequential(first_program::Union{Program,Nothing}, second_program::Union{Program,Nothing}) = Program(sequential, first_program, second_program, nothing, nothing)
Empty() = Program(empty, nothing, nothing, nothing, nothing)
DlTest(formula::Formula) = Program(dl_test, nothing, nothing, formula, nothing)

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

# TODO: Add error handling for unsupported programs, e.g. if there are more than 2 branches in a choice, or if the program uses return
function program_to_kyx(program)
    if program.head == :block
        if length(program.args) == 0
            kyx_program = Empty()
        else
            new_program = Expr(program.head, program.args[2:end]...)
            kyx_program = Sequential(program_to_kyx(program.args[1]), program_to_kyx(new_program))
        end
    elseif program.head == :if
        # TODO: Handle the case where there is no else branch and when there are more than 2 branches
        if_formula = formula_to_kyx(program.args[1])
        if_condition = DlTest(if_formula)
        if_block = program_to_kyx(program.args[2])
        else_formula = Formula(Elenchos.not, if_formula, nothing, nothing, nothing)
        else_condition = DlTest(else_formula)
        if length(program.args) == 2
            else_block = Empty()
        elseif length(program.args) == 3
            else_block = program_to_kyx(program.args[3])
        end
        first_choice = Sequential(if_condition, if_block)
        second_choice = Sequential(else_condition, else_block)
        kyx_program = Choice(first_choice, second_choice)
    elseif program.head == :(=)
        kyx_program = Assignment(expression_to_kyx(program.args[1]), expression_to_kyx(program.args[2]))
    end
    return kyx_program
end

function expression_to_string(expression::Expression)
    symbol_to_string = Dict(
        plus => "+",
        minus => "-",
        mult => "*",
        Elenchos.div => "/"
    )
    if expression.symbol == symbol
        #TODO: Handle the edge cases, e.g., x_1, x_2, etc.
        return snake_case_to_camel_case("$(expression.left)")
    elseif expression.symbol == Elenchos.real
        return "$(expression.left)"
    elseif expression.symbol in [plus, minus, mult, Elenchos.div]
        return "$(expression_to_string(expression.left)) " * symbol_to_string[expression.symbol] * " $(expression_to_string(expression.right))"
    end
end


function formula_to_string(formula::Formula)
    symbol_to_string = Dict(
        less_or_equal => "<=",
        greater_or_equal => ">=",
        Elenchos.less => "<",
        greater => ">",
        equal => "=",
        not_equal => "!=",
        and => "&",
        or => "|",
        not => "!",
        bool_true => "true",
        bool_false => "false"
    )
    if formula.symbol in [less_or_equal, greater_or_equal, Elenchos.less, greater, equal, not_equal]
        return "$(expression_to_string(formula.first_expressions)) " * symbol_to_string[formula.symbol] * " $(expression_to_string(formula.second_expressions))"
    elseif formula.symbol in [and, or]
        return "$(formula_to_string(formula.first_subformula)) " * symbol_to_string[formula.symbol] * " $(formula_to_string(formula.second_subformula))"
    elseif formula.symbol == not
        return symbol_to_string[formula.symbol] * "($(formula_to_string(formula.first_subformula)))"
    elseif formula.symbol in [bool_true, bool_false]
        return symbol_to_string[formula.symbol]
    end
end


function program_to_string(program::Program)
    symbol_to_string = Dict(
        assign => ":=",
        choice => "∪",
        sequential => ";",
        dl_test => "?"
    )
    if program.symbol == assign
        return "$(expression_to_string(program.expressions[1])) " * symbol_to_string[program.symbol] * " $(expression_to_string(program.expressions[2]))"
    elseif program.symbol == choice
        return "{$(program_to_string(program.first_programs)) " * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))}"
    elseif program.symbol == sequential
        return "$(program_to_string(program.first_programs))" * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))"
    elseif program.symbol == dl_test
        return symbol_to_string[program.symbol] * "($(formula_to_string(program.formula)))"
    elseif program.symbol == empty
        return ""
    end
end

export expression_to_string, formula_to_string, program_to_string
export ExpressionSymbol, plus, minus, mult, div, real, symbol
export FormulaSymbol, less_or_equal, greater_or_equal, less, greater, equal, not_equal, and, or, not, bool_true, bool_false
export expression_to_kyx, formula_to_kyx, Expression, Formula
export Not, And, Or, LessOrEqual, GreaterOrEqual, Less, Greater, Equal, NotEqual, BoolTrue, BoolFalse
export ProgramSymbol, assign, choice, sequential, dl_test
export Program, Assignment, Choice, Sequential, Empty, DlTest
export program_to_kyx
export DlReal, DlSymbol, Plus, Minus, Mult, Div