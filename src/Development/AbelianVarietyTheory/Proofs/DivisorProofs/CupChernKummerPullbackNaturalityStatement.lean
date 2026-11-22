module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_chern_kummer_pullback_naturality : GlobalTheory.EtC.DivisorNaturality := by
  first | (exact @GlobalTheory.EtC.a6nat_holds) | (exact GlobalTheory.EtC.a6nat_holds) | (intros; apply GlobalTheory.EtC.a6nat_holds  <;> assumption)
