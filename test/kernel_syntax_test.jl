using Test
using Elenchos.Kernel

@testset "Kernel Syntax (Terms & Formulas)" begin
    @testset "Terms & Term Equality" begin
        x = Variable("x")
        y = Variable("y")
        c1 = Constant(1)
        c2 = Constant(2)
        c1_rat = Constant(1//1)
        h1 = Hole(1)
        f_sym = FunctionSymbol("f")
        f_app = FunctionApplication(f_sym, (x, c1))

        @test x == Variable("x")
        @test x != y
        @test c1 == c1_rat
        @test h1 == Hole(1)
        @test_throws ArgumentError Hole(0)
        @test f_app == FunctionApplication(FunctionSymbol("f"), (Variable("x"), Constant(1)))

        # Arithmetic Terms
        @test Sum(x, c1) == Sum(x, Constant(1))
        @test Difference(x, y) != Difference(y, x)
        @test Product(c1, c2) == Product(Constant(1), Constant(2))
        @test Division(x, c2) == Division(x, Constant(2))
        @test Power(x, c2) == Power(x, Constant(2))

        # Hashing properties
        @test hash(x) == hash(Variable("x"))
        @test hash(c1) == hash(c1_rat)
        @test hash(f_app) == hash(FunctionApplication(FunctionSymbol("f"), (Variable("x"), Constant(1))))
        @test hash(Sum(x, y)) == hash(Sum(Variable("x"), Variable("y")))
    end

    @testset "Formulas & Formula Equality" begin
        x = Variable("x")
        c1 = Constant(1)
        P_sym = PredicateSymbol("P")
        P_app = PredicateApplication(P_sym, (x,))

        @test LessThan(x, c1) == LessThan(Variable("x"), Constant(1))
        @test Equals(x, x) == Equals(x, x)
        @test P_app == PredicateApplication(PredicateSymbol("P"), (x,))

        not_F = Not(Equals(x, c1))
        impl_F = Implies(LessThan(x, c1), P_app)
        forall_F = Forall(x, P_app)

        @test not_F == Not(Equals(Variable("x"), Constant(1)))
        @test impl_F == Implies(LessThan(x, c1), P_app)
        @test forall_F == Forall(Variable("x"), P_app)

        # Hashing formulas
        @test hash(not_F) == hash(Not(Equals(Variable("x"), Constant(1))))
        @test hash(forall_F) == hash(Forall(Variable("x"), P_app))
        @test hash(impl_F) == hash(Implies(LessThan(x, c1), P_app))
    end
end
