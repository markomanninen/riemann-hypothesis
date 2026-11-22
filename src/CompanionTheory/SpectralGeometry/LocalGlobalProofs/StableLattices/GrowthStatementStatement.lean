module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists

@[expose] public section

theorem _root_.GlobalTheory.T.GrowthStatement : CompanionTheory.RgExh.Dec.L.Growth :=
  GlobalTheory.CompanionTheory.PathGrowth.growth
