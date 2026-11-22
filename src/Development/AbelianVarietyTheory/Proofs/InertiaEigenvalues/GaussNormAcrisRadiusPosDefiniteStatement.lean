module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcrisRadius_pos_definite : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → 0 < gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.gC_pos_target | exact GlobalTheory.PMon.Gauss.gC_pos_target | (intros; apply GlobalTheory.PMon.Gauss.gC_pos_target <;> assumption)
