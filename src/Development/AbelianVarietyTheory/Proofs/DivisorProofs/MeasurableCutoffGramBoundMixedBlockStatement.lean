module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
