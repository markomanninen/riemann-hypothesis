module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_log_mul_le_size_ratio : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  first | exact @GlobalTheory.scale_log_mul_b'_le_b | exact GlobalTheory.scale_log_mul_b'_le_b | (intros; apply GlobalTheory.scale_log_mul_b'_le_b <;> assumption)
