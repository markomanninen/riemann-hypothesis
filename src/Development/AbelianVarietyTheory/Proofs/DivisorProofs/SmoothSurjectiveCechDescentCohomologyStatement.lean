module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_a2 : GlobalTheory.EtC.A2 := by
  first | exact @GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | exact GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology | (intros; apply GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology <;> assumption)
