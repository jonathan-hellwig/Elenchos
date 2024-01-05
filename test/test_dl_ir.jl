import Test
using MacroTools, Elenchos

begin
    program = Base.remove_linenums!(
        quote
        end
    )
    @Test.test program_to_kyx(program) == Empty()

    program = Base.remove_linenums!(
        quote
            x = 1
        end
    )
    @Test.test program_to_kyx(program) == Sequential(Assignment(DlSymbol(:x), DlReal(1)), Empty())
    
    program = :(x = 1)
    @Test.test program_to_kyx(program) == Assignment(DlSymbol(:x), DlReal(1))

    program = Base.remove_linenums!(:( if true else end))
    @Test.test program_to_kyx(program) == Choice(
        Sequential(
            DlTest(BoolTrue()),
            Empty()),
        Sequential(
            DlTest(Not(BoolTrue())),
            Empty()
        )
    )
end

begin
    formula = :(true)
    @Test.test formula_to_kyx(formula) == BoolTrue()

    formula = :(false)
    @Test.test formula_to_kyx(formula) == BoolFalse()

    formula = :(0.0 <= x)
    @Test.test formula_to_kyx(formula) == LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 < x)
    @Test.test formula_to_kyx(formula) == Less(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 >= x)
    @Test.test formula_to_kyx(formula) == GreaterOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 > x)
    @Test.test formula_to_kyx(formula) == Greater(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 == x)
    @Test.test formula_to_kyx(formula) == Equal(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 != x)
    @Test.test formula_to_kyx(formula) == NotEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing))

    formula = :(0.0 <= x && x <= 1.0)
    @Test.test formula_to_kyx(formula) == And(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(0.0 <= x || x <= 1.0)
    @Test.test formula_to_kyx(formula) == Or(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)), LessOrEqual(Expression(symbol, :x, nothing), Expression(Elenchos.real, 1.0, nothing)))

    formula = :(!(0.0 <= x))
    @Test.test formula_to_kyx(formula) == Not(LessOrEqual(Expression(Elenchos.real, 0.0, nothing), Expression(symbol, :x, nothing)))
end

begin
    expression = :(1.0 + 1.2)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 + (1.2 + 1.3)) 
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(plus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 + 1.2) + 1.3)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    epression = :(1.0 + 1.2 + 1.3)
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 - 1.2)
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 - (1.2 - 1.3))
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(minus, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 - 1.2) - 1.3)
    @Test.test expression_to_kyx(expression) == Expression(minus, Expression(minus, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 * (1.2 * 1.3))
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 * 1.2) * 1.3)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 * 1.2 * 1.3)
    @Test.test expression_to_kyx(expression) == Expression(mult, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(1.0 / 1.2)
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing))

    expression = :(1.0 / (1.2 / 1.3))
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.div, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :((1.0 / 1.2) / 1.3)
    @Test.test expression_to_kyx(expression) == Expression(Elenchos.div, Expression(Elenchos.div, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))
    
    expression = :(1.0 + 1.2 * 1.3 )
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(Elenchos.real, 1.0, nothing), Expression(mult, Expression(Elenchos.real, 1.2, nothing), Expression(Elenchos.real, 1.3, nothing)))

    expression = :(1.0 * 1.2 + 1.3 )
    @Test.test expression_to_kyx(expression) == Expression(plus, Expression(mult, Expression(Elenchos.real, 1.0, nothing), Expression(Elenchos.real, 1.2, nothing)), Expression(Elenchos.real, 1.3, nothing))

    expression = :(x)
    @Test.test expression_to_kyx(expression) == Expression(symbol, :x, nothing)
end