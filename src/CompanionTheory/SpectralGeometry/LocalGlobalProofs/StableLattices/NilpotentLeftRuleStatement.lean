module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRule
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.NilpotentLeftRule : CompanionTheory.RgExh.Dec.N.LeftRule := by
  first | exact @GlobalTheory.CompanionTheory.PathCoef.leftRule | exact GlobalTheory.CompanionTheory.PathCoef.leftRule | (intros; apply GlobalTheory.CompanionTheory.PathCoef.leftRule <;> assumption)
