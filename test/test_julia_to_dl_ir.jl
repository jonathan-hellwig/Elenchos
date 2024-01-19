import Test
using MacroTools
import Elenchos
using Elenchos: program_to_dl_ir, formula_to_dl_ir, expression_to_dl_ir
using Elenchos: DlReal, DlSymbol, DlTest, BoolTrue, BoolFalse, Less, GreaterOrEqual, NotEqual, LessOrEqual, Greater, Equal, And, Or, Not, Plus, Minus, Mult, Div, Assignment, Sequential, Choice, Empty
using Elenchos: SYMBOL, PLUS, MINUS, MULT, DIV, REAL, less_or_equal, greater_or_equal, less, greater, equal, not_equal, and, or, not, bool_true, bool_false, assign, choice, sequential, dl_test
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
            DlTest(GreaterOrEqual(Expression(SYMBOL, :x, nothing), Expression(SYMBOL, :y, nothing))),
            Sequential(
                Assignment(DlSymbol(:max_value), Expression(SYMBOL, :x, nothing)),
                Empty()
            )
        ),
        Sequential(
            DlTest(Not(GreaterOrEqual(Expression(SYMBOL, :x, nothing), Expression(SYMBOL, :y, nothing)))),
            Sequential(
                Assignment(DlSymbol(:max_value), Expression(SYMBOL, :y, nothing)),
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
    @Test.test formula_to_dl_ir(formula) == LessOrEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 < x)
    @Test.test formula_to_dl_ir(formula) == Less(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 >= x)
    @Test.test formula_to_dl_ir(formula) == GreaterOrEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 > x)
    @Test.test formula_to_dl_ir(formula) == Greater(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 == x)
    @Test.test formula_to_dl_ir(formula) == Equal(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 != x)
    @Test.test formula_to_dl_ir(formula) == NotEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing))

    formula = :(0.0 <= x && x <= 1.0)
    @Test.test formula_to_dl_ir(formula) == And(LessOrEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing)), LessOrEqual(Expression(SYMBOL, :x, nothing), Expression(Elenchos.REAL, 1.0, nothing)))

    formula = :(0.0 <= x || x <= 1.0)
    @Test.test formula_to_dl_ir(formula) == Or(LessOrEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing)), LessOrEqual(Expression(SYMBOL, :x, nothing), Expression(Elenchos.REAL, 1.0, nothing)))

    formula = :(!(0.0 <= x))
    @Test.test formula_to_dl_ir(formula) == Not(LessOrEqual(Expression(Elenchos.REAL, 0.0, nothing), Expression(SYMBOL, :x, nothing)))
end

@Test.testset "Test expression_to_dl_ir" begin
    expression = :(1.0 + 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing))

    expression = :(1.0 + (1.2 + 1.3)) 
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(PLUS, Expression(Elenchos.REAL, 1.2, nothing), Expression(Elenchos.REAL, 1.3, nothing)))

    expression = :((1.0 + 1.2) + 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(PLUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    epression = :(1.0 + 1.2 + 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(PLUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    expression = :(1.0 - 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(MINUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing))

    expression = :(1.0 - (1.2 - 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(MINUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(MINUS, Expression(Elenchos.REAL, 1.2, nothing), Expression(Elenchos.REAL, 1.3, nothing)))

    expression = :((1.0 - 1.2) - 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(MINUS, Expression(MINUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    expression = :(1.0 * 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(MULT, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing))

    expression = :(1.0 * (1.2 * 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(MULT, Expression(Elenchos.REAL, 1.0, nothing), Expression(MULT, Expression(Elenchos.REAL, 1.2, nothing), Expression(Elenchos.REAL, 1.3, nothing)))

    expression = :((1.0 * 1.2) * 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(MULT, Expression(MULT, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    expression = :(1.0 * 1.2 * 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(MULT, Expression(MULT, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    expression = :(1.0 / 1.2)
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.DIV, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing))

    expression = :(1.0 / (1.2 / 1.3))
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.DIV, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.DIV, Expression(Elenchos.REAL, 1.2, nothing), Expression(Elenchos.REAL, 1.3, nothing)))

    expression = :((1.0 / 1.2) / 1.3)
    @Test.test expression_to_dl_ir(expression) == Expression(Elenchos.DIV, Expression(Elenchos.DIV, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))
    
    expression = :(1.0 + 1.2 * 1.3 )
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(Elenchos.REAL, 1.0, nothing), Expression(MULT, Expression(Elenchos.REAL, 1.2, nothing), Expression(Elenchos.REAL, 1.3, nothing)))

    expression = :(1.0 * 1.2 + 1.3 )
    @Test.test expression_to_dl_ir(expression) == Expression(PLUS, Expression(MULT, Expression(Elenchos.REAL, 1.0, nothing), Expression(Elenchos.REAL, 1.2, nothing)), Expression(Elenchos.REAL, 1.3, nothing))

    expression = :(x)
    @Test.test expression_to_dl_ir(expression) == Expression(SYMBOL, :x, nothing)

    expression = :(-x)
    @Test.test expression_to_dl_ir(expression) == Expression(MINUS, Expression(SYMBOL, :x, nothing), nothing)
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