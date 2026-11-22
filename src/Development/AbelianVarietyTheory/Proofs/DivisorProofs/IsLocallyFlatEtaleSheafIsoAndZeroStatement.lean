module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  first | exact @GlobalTheory.EtC.flatS_iso_and_zero | exact GlobalTheory.EtC.flatS_iso_and_zero | (intros; apply GlobalTheory.EtC.flatS_iso_and_zero <;> assumption)
