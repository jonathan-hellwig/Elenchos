import Test
using Elenchos


function expression_to_string(expression::Expression)
    symbol_to_string = Dict(
        plus => "+",
        minus => "-",
        mult => "*",
        Elenchos.div => "/"
    )
    if expression.symbol == symbol
        return "$(expression.left)"
    elseif expression.symbol == Elenchos.real
        return "$(expression.left)"
    elseif expression.symbol in [plus, minus, mult, Elenchos.div]
        return "$(expression_to_string(expression.left)) " * symbol_to_string[expression.symbol] * " $(expression_to_string(expression.right))"
    end
end

@Test.test expression_to_string(DlSymbol(:x)) == "x"

@Test.test expression_to_string(DlReal(1.0)) == "1.0"

@Test.test expression_to_string(Plus(DlSymbol(:x), DlReal(1.0))) == "x + 1.0"

@Test.test expression_to_string(Minus(DlSymbol(:x), DlReal(1.0))) == "x - 1.0"

@Test.test expression_to_string(Mult(DlSymbol(:x), DlReal(1.0))) == "x * 1.0"

@Test.test expression_to_string(Div(DlSymbol(:x), DlReal(1.0))) == "x / 1.0"

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

@Test.test formula_to_string(BoolTrue()) == "true"
@Test.test formula_to_string(BoolFalse()) == "false"
@Test.test formula_to_string(Not(BoolTrue())) == "!(true)"
@Test.test formula_to_string(Not(BoolFalse())) == "!(false)"

@Test.test formula_to_string(LessOrEqual(DlSymbol(:x), DlReal(1.0))) == "x <= 1.0"
@Test.test formula_to_string(And(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4)))) == "3 > 2 & 4 = 4"
@Test.test formula_to_string(Or(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4)))) == "3 > 2 | 4 = 4"
@Test.test formula_to_string(Not(Or(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4))))) == "!(3 > 2 | 4 = 4)"


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
        return "$(program_to_string(program.first_programs)) " * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))"
    elseif program.symbol == sequential
        return "$(program_to_string(program.first_programs))" * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))"
    elseif program.symbol == dl_test
        return symbol_to_string[program.symbol] * "($(formula_to_string(program.formula)))"
    end
end

@Test.test program_to_string(Assignment(DlSymbol(:x), DlReal(1.0))) == "x := 1.0"
@Test.test program_to_string(Sequential(Assignment(DlSymbol(:x), DlReal(1.0)), Assignment(DlSymbol(:y), DlReal(2.0)))) == "x := 1.0; y := 2.0"
@Test.test program_to_string(Choice(Assignment(DlSymbol(:x), DlReal(1.0)), Assignment(DlSymbol(:y), DlReal(2.0)))) == "x := 1.0 ∪ y := 2.0"
@Test.test program_to_string(DlTest(BoolTrue())) == "?(true)"