module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowCountAllBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_count_all_bounds : FactorialWeightedSumBound ∧ FactorialMultiindexBound ∧ RadiusExponentInequality := by
  first | exact @GlobalTheory.LowCount.lowC_all | exact GlobalTheory.LowCount.lowC_all | (intros; apply GlobalTheory.LowCount.lowC_all <;> assumption)
