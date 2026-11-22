module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.a6ring_holds : GlobalTheory.EtC.DivisorRingCompatibility := by
  intro q _ E
  exact ⟨fun hE _ _ a => (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a,
    fun a b c => GlobalTheory.T.tateTwistCupProduct_assoc q E a b c,
    fun a b => GlobalTheory.T.tateTwistCupProduct_graded_comm q E a b⟩

end GlobalTheory
