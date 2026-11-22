module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
