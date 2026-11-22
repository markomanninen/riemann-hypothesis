module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFlip_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor) := by
  first | exact @GlobalTheory.EtC.Pair.exists_isFlip | exact GlobalTheory.EtC.Pair.exists_isFlip | (intros; apply GlobalTheory.EtC.Pair.exists_isFlip <;> assumption)
