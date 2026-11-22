module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequence
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficient_longExactSequence : GlobalTheory.EtC.A7 := by
  first | (exact @GlobalTheory.EtC.coefSeq_exact) | (exact GlobalTheory.EtC.coefSeq_exact) | (intros; apply GlobalTheory.EtC.coefSeq_exact  <;> assumption)
