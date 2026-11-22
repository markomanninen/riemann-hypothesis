module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | exact GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | (intros; apply GlobalTheory.IntBall.lintegral_hB_one_two_lt_top <;> assumption)
