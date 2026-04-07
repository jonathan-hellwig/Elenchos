using Test
using Elenchos
using Elenchos.Kernel
using Elenchos.Syntax
using Elenchos.Serialization
using Elenchos.Theorems

@testset "Proof Serialization and Deserialization" begin

    # Basic definitions
    x, y = Variable("x"), Variable("y")
    P = PredicateSymbol("P")
    Q = PredicateSymbol("Q")
    Px = PredicateApplication(P, (x,))
    Qx = PredicateApplication(Q, (x,))

    # Helper to retrieve the original rule that was applied at the root
    function get_root_rule(d::Derivation)
        while typeof(d.rule) == ApplySubproof
            d = d.children[1]
        end
        return d.rule
    end

    @testset "Assume Rule" begin
        seq = Sequent((Px,), (Px,))
        deriv = Derivation(Assume(seq))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == Assume
    end

    @testset "Axiom Rule" begin
        ax_form = Implies(Equals(_x, _y), Equals(_C_sym(_x), _C_sym(_y)))
        ax = KernelAxiom(ax_form)
        deriv = Derivation(AxiomRule(AX_CONG_CONTEXT))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == Sequent((), (AX_CONG_CONTEXT.formula,))
        @test typeof(get_root_rule(deriv2)) == AxiomRule
        @test get_root_rule(deriv2).axiom.formula == AX_CONG_CONTEXT.formula
    end

    @testset "NotRight Rule" begin
        seq = Sequent((Px,), ())
        asm_deriv = Derivation(Assume(seq))
        deriv = Derivation(NotRightRule(Sequent((), (Not(Px),)), Cons(1), Ante(1)))
        deriv = Derivation(deriv, 1, asm_deriv)

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == Sequent((), (Not(Px),))
        @test typeof(get_root_rule(deriv2)) == NotRightRule
    end

    @testset "ImpliesRight Rule" begin
        seq = Sequent((Px,), (Qx,))
        asm_deriv = Derivation(Assume(seq))
        deriv = Derivation(ImpliesRightRule(Sequent((), (Implies(Px, Qx),)), Cons(1), Ante(1)))
        deriv = Derivation(deriv, 1, asm_deriv)

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == Sequent((), (Implies(Px, Qx),))
        @test typeof(get_root_rule(deriv2)) == ImpliesRightRule
    end

    @testset "Close Rule" begin
        seq = Sequent((Px,), (Px,))
        deriv = Derivation(CloseRule(seq, Ante(1), Cons(1)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == CloseRule
    end

    @testset "GroundInequalityRightRule" begin
        c1 = Constant(1)
        c2 = Constant(2)
        deriv = Derivation(GroundInequalityRightRule(c1, c2))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        expected_seq = Sequent((), (LessThan(c1, c2),))
        @test deriv2.conclusion == expected_seq
        @test typeof(get_root_rule(deriv2)) == GroundInequalityRightRule
    end

    @testset "ForallRight Rule" begin
        Py = PredicateApplication(P, (y,))
        seq = Sequent((Px,), (Forall(y, Py),))
        # The fresh variable used in the rule is x, which is not free in the sequent? Wait. Px has x.
        # So x is NOT fresh for the sequent (Px,) ⊢ (Forall(y, P(y)),).
        # We must use a truly fresh variable, e.g., z.
        z = Variable("z")
        deriv = Derivation(ForallRightRule(seq, Cons(1), z))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == ForallRightRule
    end

    @testset "ImpliesLeft Rule" begin
        seq = Sequent((Implies(Px, Qx),), (Qx,))
        deriv = Derivation(ImpliesLeftRule(seq, Ante(1), Cons(1)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == ImpliesLeftRule
    end

    @testset "NotLeft Rule" begin
        seq = Sequent((Not(Px),), ())
        deriv = Derivation(NotLeftRule(seq, Ante(1), Cons(1)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == NotLeftRule
    end

    @testset "Substitution Rule" begin
        seq = Sequent((PredicateApplication(P, (_x,)),), (PredicateApplication(P, (_x,)),))
        σ = Substitution(_x_sym => Constant(5))
        deriv = Derivation(SubstitutionRule(seq, σ))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        expected_concl = Sequent((PredicateApplication(P, (Constant(5),)),), (PredicateApplication(P, (Constant(5),)),))
        @test deriv2.conclusion == expected_concl
        @test typeof(get_root_rule(deriv2)) == SubstitutionRule
    end

    @testset "WeakeningLeft Rule" begin
        seq = Sequent((Px, Qx), (Px,))
        deriv = Derivation(WeakeningLeftRule(seq, Ante(2)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == WeakeningLeftRule
    end

    @testset "WeakeningRight Rule" begin
        seq = Sequent((Px,), (Px, Qx))
        deriv = Derivation(WeakeningRightRule(seq, Cons(2)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == WeakeningRightRule
    end

    @testset "Cut Rule" begin
        seq = Sequent((Px,), (Qx,))
        cut_form = PredicateApplication(PredicateSymbol("R"), (x,))
        deriv = Derivation(CutRule(seq, cut_form, Cons(1), Ante(1)))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        @test deriv2.conclusion == seq
        @test typeof(get_root_rule(deriv2)) == CutRule
    end

    @testset "GroundInequalityLeftRule" begin
        c1 = Constant(3)
        c2 = Constant(1)
        deriv = Derivation(GroundInequalityLeftRule(c1, c2))

        cert = serialize_proof(deriv)
        deriv2 = deserialize_proof(cert)

        expected_seq = Sequent((LessThan(c1, c2),), ())
        @test deriv2.conclusion == expected_seq
        @test typeof(get_root_rule(deriv2)) == GroundInequalityLeftRule
    end

end
