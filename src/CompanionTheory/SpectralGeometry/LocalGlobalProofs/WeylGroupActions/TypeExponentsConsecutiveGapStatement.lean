module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TypeExponentsConsecutiveGap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.FrameExists2
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_exponents_consecutive_gap : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Ico 1 k, u (i + 1) + 1 ≤ u i) → ∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | exact GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one | (intros; apply GlobalTheory.CompanionTheory.TypeGaps.gap_eq_nat_add_one <;> assumption)
