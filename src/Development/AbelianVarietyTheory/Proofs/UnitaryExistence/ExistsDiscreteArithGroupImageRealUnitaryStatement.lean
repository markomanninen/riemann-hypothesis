module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized

@[expose] public section

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discrete_arithGroupImage_realUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  first | exact @GlobalTheory.ArithImage.exists_discrete_image | exact GlobalTheory.ArithImage.exists_discrete_image | (intros; apply GlobalTheory.ArithImage.exists_discrete_image <;> assumption)
