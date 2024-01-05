import Test
using Elenchos

@Test.testset "Test expression_to_string" begin
    @Test.test expression_to_string(DlSymbol(:x)) == "x"
    @Test.test expression_to_string(DlReal(1.0)) == "1.0"
    @Test.test expression_to_string(Plus(DlSymbol(:x), DlReal(1.0))) == "x + 1.0"
    @Test.test expression_to_string(Minus(DlSymbol(:x), DlReal(1.0))) == "x - 1.0"
    @Test.test expression_to_string(Mult(DlSymbol(:x), DlReal(1.0))) == "x * 1.0"
    @Test.test expression_to_string(Div(DlSymbol(:x), DlReal(1.0))) == "x / 1.0"
end

@Test.testset "Test formula_to_string" begin
    @Test.test formula_to_string(BoolTrue()) == "true"
    @Test.test formula_to_string(BoolFalse()) == "false"
    @Test.test formula_to_string(Not(BoolTrue())) == "!(true)"
    @Test.test formula_to_string(Not(BoolFalse())) == "!(false)"

    @Test.test formula_to_string(LessOrEqual(DlSymbol(:x), DlReal(1.0))) == "x <= 1.0"
    @Test.test formula_to_string(And(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4)))) == "3 > 2 & 4 = 4"
    @Test.test formula_to_string(Or(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4)))) == "3 > 2 | 4 = 4"
    @Test.test formula_to_string(Not(Or(Greater(DlReal(3), DlReal(2)), Equal(DlReal(4),DlReal(4))))) == "!(3 > 2 | 4 = 4)"
end

@Test.testset "Test program_to_string" begin
    @Test.test program_to_string(Assignment(DlSymbol(:x), DlReal(1.0))) == "x := 1.0"
    @Test.test program_to_string(Sequential(Assignment(DlSymbol(:x), DlReal(1.0)), Assignment(DlSymbol(:y), DlReal(2.0)))) == "x := 1.0; y := 2.0"
    @Test.test program_to_string(Choice(Assignment(DlSymbol(:x), DlReal(1.0)), Assignment(DlSymbol(:y), DlReal(2.0)))) == "{x := 1.0 ∪ y := 2.0}"
    @Test.test program_to_string(DlTest(BoolTrue())) == "?(true)"
    @Test.test program_to_string(Empty()) == ""
end