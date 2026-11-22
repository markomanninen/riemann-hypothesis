module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  first | (exact @GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (exact GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (intros; apply GlobalTheory.EtC.cpull_bijective_of_quasiIso  <;> assumption)
