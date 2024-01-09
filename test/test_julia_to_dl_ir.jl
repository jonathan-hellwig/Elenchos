import Test
using MacroTools
import Elenchos
using Elenchos: program_to_dl_ir, formula_to_dl_ir, expression_to_dl_ir
using Elenchos: DlReal, DlSymbol, DlTest, BoolTrue, BoolFalse, Less, GreaterOrEqual, NotEqual, LessOrEqual, Greater, Equal, And, Or, Not, Plus, Minus, Mult, Div, Assignment, Sequential, Choice, Empty
using Elenchos: symbol, plus, minus, mult, div, real, less_or_equal, greater_or_equal, less, greater, equal, not_equal, and, or, not, bool_true, bool_false, assign, choice, sequential, dl_test
using Elenchos: Program, Expression, Formula, ExpressionSymbol, FormulaSymbol, ProgramSymbol
using Elenchos: get_variables, get_modified_variables

@Test.testset "Test program_to_dl_ir" begin
    program = Base.remove_linenums!(
        quote
        end
    )
    @Test.test program_to_dl_ir(program) == Empty()

    program = Base.remove_linenums!(
        quote
            x = 1
        end
    )
    @Test.test program_to_dl_ir(program) == Sequential(Assignment(DlSymbol(:x), DlReal(1)), Empty())
    
    program = :(x = 1)
    @Test.test program_to_dl_ir(program) == Assignment(DlSymbol(:x), DlReal(1))

    program = Base.remove_linenums!(:( if true else end))
    @Test.test program_to_dl_ir(program) == Choice(
        Sequential(
            DlTest(BoolTrue()),
            Empty()),
        Sequential(
            DlTest(Not(BoolTrue())),
            Empty()
        )
    )
    program = Base.remove_linenums!(quote
        if x >= y
            max_value = x
        else
            max_value = y
        end
    end)
    @Test.test program_to_dl_ir(program) == Sequential(Choice(
        Sequential(
            DlTest(GreaterOrEqual(Expression(symbol, :x, nothing), Expression(symbol, :y, nothing))),
            Sequential(
                Assignment(DlSymbol(:max_value), Expression(symbol, :x, nothing)),
                Empty()
            )
        ),
        Sequential(
            DlTest(Not(GreaterOrEqual(Expression(symbol, :x, nothing), Expression(symbol, :y, nothing)))),
            Sequential(
                Assignment(DlSymbol(:max_value), Expression(symbol, :y, nothing)),
                Empty()
            )
        )
    ), Empty())
end

@Test.testset "Test formula_to_dl_ir" begin
    formula = :(true)
    @Test.test formula_to_dl_ir(formula) == BoolTrue()

    formula = :(false)
    @Test.test formula_to_dl_ir(formula) == BoolFalse()

    formula = :(0.0 <= x)
    @Test.test formula_to_dl_ir(formula) == LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 < x)
    @Test.test formula_to_dl_ir(formula) == Less(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 >= x)
    @Test.test formula_to_dl_ir(formula) == GreaterOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 > x)
    @Test.test formula_to_dl_ir(formula) == Greater(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 == x)
    @Test.test formula_to_dl_ir(formula) == Equal(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 != x)
    @Test.test formula_to_dl_ir(formula) == NotEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 <= x && x <= 1.0)
    @Test.test formula_to_dl_ir(formula) == And(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(0.0 <= x || x <= 1.0)
    @Test.test formula_to_dl_ir(formula) == Or(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(!(0.0 <= x))
    @Test.test formula_to_dl_ir(formula) == Not(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)))
end

@Test.testset "Test expression_to_dl_ir" begin
    expression = :(1.0 + 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 + (1.2 + 1.3)) 
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(plus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 + 1.2) + 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    epression = :(1.0 + 1.2 + 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 - 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 - (1.2 - 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(minus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 - 1.2) - 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(minus, Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 * (1.2 * 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 * 1.2) * 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2 * 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 / 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 / (1.2 / 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.div, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 / 1.2) / 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.div, Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))
    
    expression = :(1.0 + 1.2 * 1.3 )
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :(1.0 * 1.2 + 1.3 )
    @Test.test expression_to_dl_ir(expression) == Expression(plus, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(x)
    @Test.test expression_to_dl_ir(expression) == Expression(symbol, :x, nothing)
end

@Test.testset "Test get_variables" begin
    @Test.test get_variables(DlReal(0.0)) == Set()
    @Test.test get_variables(DlSymbol(:x)) == Set([:x])
    @Test.test get_variables(Plus(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Plus(DlSymbol(:x), DlReal(0.0))) == Set([:x])
    @Test.test get_variables(Plus(DlSymbol(:x), DlSymbol(:y))) == Set([:x, :y])
    @Test.test get_variables(Plus(DlReal(0.0), Plus(DlSymbol(:x), DlSymbol(:y)))) == Set([:x, :y])
    @Test.test get_variables(Minus(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Div(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Mult(DlReal(0.0), DlSymbol(:x))) == Set([:x])

    @Test.test get_variables(BoolTrue()) == Set()
    @Test.test get_variables(BoolFalse()) == Set()
    @Test.test get_variables(LessOrEqual(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(GreaterOrEqual(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Less(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Greater(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(Equal(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(NotEqual(DlReal(0.0), DlSymbol(:x))) == Set([:x])
    @Test.test get_variables(And(BoolTrue(), BoolFalse())) == Set()
    @Test.test get_variables(Or(BoolTrue(), BoolFalse())) == Set()
    @Test.test get_variables(Not(BoolTrue())) == Set()
end

@Test.testset "Test get_modified_variables" begin
    @Test.test get_modified_variables(Sequential(Assignment(DlSymbol(:x), DlReal(1)), Empty())) == Set([:x])
    @Test.test get_modified_variables(Choice(Sequential(Assignment(DlSymbol(:x), DlReal(1)), Empty()), Sequential(Assignment(DlSymbol(:y), DlReal(1)), Empty()))) == Set([:x, :y])
end