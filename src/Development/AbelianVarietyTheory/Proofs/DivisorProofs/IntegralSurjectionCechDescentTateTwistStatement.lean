module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSurjection_cechDescent_tateTwist : GlobalTheory.EtC.B4 := by
  first | (exact @GlobalTheory.EtC.b4) | (exact GlobalTheory.EtC.b4) | (intros; apply GlobalTheory.EtC.b4  <;> assumption)
