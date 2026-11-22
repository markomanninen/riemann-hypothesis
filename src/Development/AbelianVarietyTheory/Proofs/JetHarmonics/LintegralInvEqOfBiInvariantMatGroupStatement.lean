module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.PeriodIntegrals.QuotSetU
public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  first | exact @GlobalTheory.HaarInversion.lintegral_inv_eq | exact GlobalTheory.HaarInversion.lintegral_inv_eq | (intros; apply GlobalTheory.HaarInversion.lintegral_inv_eq <;> assumption)
