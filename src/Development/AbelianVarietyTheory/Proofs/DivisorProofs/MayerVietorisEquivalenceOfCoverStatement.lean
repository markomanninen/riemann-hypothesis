module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayerVietoris_equivalence_of_cover : GlobalTheory.EtC.A4 := by
  first | (exact @GlobalTheory.MayerVietorisEqv.a4) | (exact GlobalTheory.MayerVietorisEqv.a4) | (intros; apply GlobalTheory.MayerVietorisEqv.a4  <;> assumption)
