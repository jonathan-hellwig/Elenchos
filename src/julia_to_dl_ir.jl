@enum ExpressionSymbol PLUS MINUS MULT DIV REAL SYMBOL

struct Expression
    symbol::ExpressionSymbol
    left::Union{Expression,Symbol,Real}
    right::Union{Expression,Nothing}
end
Plus(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(PLUS, left, right)
Minus(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(MINUS, left, right)
Mult(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(MULT, left, right)
Div(left::Union{Expression,Symbol,Real}, right::Union{Expression,Symbol,Real}) = Expression(DIV, left, right)
DlReal(value::Real) = Expression(REAL, value, nothing)
DlSymbol(dlsymbol::Symbol) = Expression(SYMBOL, dlsymbol, nothing)

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

function expression_to_dl_ir(expression)
    if isa(expression, Real)
        return Expression(REAL, expression, nothing)
    elseif isa(expression, Symbol)
        return Expression(SYMBOL, expression, nothing)
    end
    if expression.head != :call
        error("Not a call expression!")
    end

    expression_symbol = expression.args[1]
    if expression_symbol == :+
        kyx_expression = Expression(PLUS, expression_to_dl_ir(expression.args[2]), expression_to_dl_ir(expression.args[3]))
        for i in 4:length(expression.args)
            kyx_expression = Expression(PLUS, kyx_expression, expression_to_dl_ir(expression.args[i]))
        end
    elseif expression_symbol == :-
        kyx_expression = Expression(MINUS, expression_to_dl_ir(expression.args[2]), expression_to_dl_ir(expression.args[3]))
    elseif expression_symbol == :*
        kyx_expression = Expression(MULT, expression_to_dl_ir(expression.args[2]), expression_to_dl_ir(expression.args[3]))
        for i in 4:length(expression.args)
            kyx_expression = Expression(MULT, kyx_expression, expression_to_dl_ir(expression.args[i]))
        end
    elseif expression_symbol == :/
        kyx_expression = Expression(DIV, expression_to_dl_ir(expression.args[2]), expression_to_dl_ir(expression.args[3]))
    else
        error("Unknown operator!")
    end
    return kyx_expression
end

#TODO: Support formulas like 0 <= x <= 1
function formula_to_dl_ir(formula)
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
        kyx_formula = Formula(symbol_to_formula[formula.head], formula_to_dl_ir(formula.args[1]), formula_to_dl_ir(formula.args[2]), nothing, nothing)
    elseif formula.head == :call
        symbol = formula.args[1]

        if symbol in [:<=, :>=, :<, :>, :(==), :!=]
            kyx_formula = Formula(symbol_to_formula[symbol], nothing, nothing, expression_to_dl_ir(formula.args[2]), expression_to_dl_ir(formula.args[3]))
        elseif symbol == :!
            kyx_formula = Formula(symbol_to_formula[symbol], formula_to_dl_ir(formula.args[2]), nothing, nothing, nothing)
        end
    end
    return kyx_formula

end
# TODO: Support return statements
# TODO: Add error handling for unsupported programs, e.g. if there are more than 2 branches in a choice, or if the program uses return
function program_to_dl_ir(program)
    if program.head == :block
        if length(program.args) == 0
            kyx_program = Empty()
        else
            new_program = Expr(program.head, program.args[2:end]...)
            kyx_program = Sequential(program_to_dl_ir(program.args[1]), program_to_dl_ir(new_program))
        end
    elseif program.head == :if
        # TODO: Handle the case where there is no else branch and when there are more than 2 branches
        if_formula = formula_to_dl_ir(program.args[1])
        if_condition = DlTest(if_formula)
        if_block = program_to_dl_ir(program.args[2])
        else_formula = Formula(Elenchos.not, if_formula, nothing, nothing, nothing)
        else_condition = DlTest(else_formula)
        if length(program.args) == 2
            else_block = Empty()
        elseif length(program.args) == 3
            else_block = program_to_dl_ir(program.args[3])
        end
        first_choice = Sequential(if_condition, if_block)
        second_choice = Sequential(else_condition, else_block)
        kyx_program = Choice(first_choice, second_choice)
    elseif program.head == :(=)
        kyx_program = Assignment(expression_to_dl_ir(program.args[1]), expression_to_dl_ir(program.args[2]))
    end
    return kyx_program
end

function get_variables(formula::Formula)
    result = Set()
    if formula.symbol == less_or_equal || formula.symbol == greater_or_equal || formula.symbol == less || formula.symbol == greater || formula.symbol == equal || formula.symbol == not_equal
        result = union(result, get_variables(formula.first_expressions))
        result = union(result, get_variables(formula.second_expressions))
        return result
    elseif formula.symbol == and || formula.symbol == or
        result = union(result, get_variables(formula.first_subformula))
        result = union(result, get_variables(formula.second_subformula))
        return result
    elseif formula.symbol == not
        result = union(result, get_variables(formula.first_subformula))
        return result
    end
    return Set()

end

function get_variables(expression::Expression)
    result = Set()
    if expression.symbol == SYMBOL
        push!(result, expression.left)
        return result
    elseif expression.symbol in [PLUS, MINUS, MULT, DIV]
        result = union(result, get_variables(expression.left))
        result = union(result, get_variables(expression.right))
        return result
    end
    return Set()
end

function get_modified_variables(program::Program)
    result = Set()
    if program.symbol == assign
        push!(result, program.expressions[1].left)
        return result
    elseif program.symbol == choice
        result = union(result, get_modified_variables(program.first_programs))
        result = union(result, get_modified_variables(program.second_programs))
        return result
    elseif program.symbol == sequential
        result = union(result, get_modified_variables(program.first_programs))
        result = union(result, get_modified_variables(program.second_programs))
        return result
    end
    return Set()
end

function Base.show(io::IO, expression::Expression)
    if expression.symbol == PLUS
        print(io, "(")
        print(io, expression.left)
        print(io, " + ")
        print(io, expression.right)
        print(io, ")")
    elseif expression.symbol == MINUS
        print(io, "(")
        print(io, expression.left)
        print(io, " - ")
        print(io, expression.right)
        print(io, ")")
    elseif expression.symbol == MULT
        print(io, "(")
        print(io, expression.left)
        print(io, " * ")
        print(io, expression.right)
        print(io, ")")
    elseif expression.symbol == DIV
        print(io, "(")
        print(io, expression.left)
        print(io, " / ")
        print(io, expression.right)
        print(io, ")")
    elseif expression.symbol == REAL
        print(io, expression.left)
    elseif expression.symbol == SYMBOL
        print(io, expression.left)
    end
end

# Formulas:
function Base.show(io::IO, formula::Formula)
    if formula.symbol == less_or_equal
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " <= ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == greater_or_equal
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " >= ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == less
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " < ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == greater
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " > ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == equal
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " == ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == not_equal
        print(io, "(")
        print(io, formula.first_expressions)
        print(io, " != ")
        print(io, formula.second_expressions)
        print(io, ")")
    elseif formula.symbol == and
        print(io, "(")
        print(io, formula.first_subformula)
        print(io, " & ")
        print(io, formula.second_subformula)
        print(io, ")")
    elseif formula.symbol == or
        print(io, "(")
        print(io, formula.first_subformula)
        print(io, " | ")
        print(io, formula.second_subformula)
        print(io, ")")
    elseif formula.symbol == not
        print(io, "!(")
        print(io, formula.first_subformula)
        print(io, ")")
    elseif formula.symbol == bool_true
        print(io, "true")
    elseif formula.symbol == bool_false
        print(io, "false")
    end
end

# Programs:
function Base.show(io::IO, program::Program)
    if program.symbol == assign
        print(io, program.expressions[1].left)
        print(io, " := ")
        print(io, program.expressions[2])
    elseif program.symbol == choice
        print(io, "(","(", program.first_programs, ")")
        print(io, " ∪ ")
        print(io, "(", program.second_programs, ")",")")
    elseif program.symbol == sequential
        print(io, program.first_programs)
        print(io, "; ")
        print(io, program.second_programs)
    elseif program.symbol == dl_test
        print(io, "?")
        print(io, program.formula)
    elseif program.symbol == empty
        print(io, "ε")
    end
end
