module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerContentValuation_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  first | exact @GlobalTheory.DetPowContent.content_detPow_bounds | exact GlobalTheory.DetPowContent.content_detPow_bounds | (intros; apply GlobalTheory.DetPowContent.content_detPow_bounds <;> assumption)
