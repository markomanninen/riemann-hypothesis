module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_extraction_lemma_sheaf : RootStatement := by
  first | exact @GlobalTheory.RootTrick.root_statement | exact GlobalTheory.RootTrick.root_statement | (intros; apply GlobalTheory.RootTrick.root_statement <;> assumption)
