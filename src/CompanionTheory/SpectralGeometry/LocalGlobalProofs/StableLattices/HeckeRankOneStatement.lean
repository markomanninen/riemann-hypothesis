module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOne
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeRankOne : CompanionTheory.RgExh.Hk.RankOne := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.rankOne | exact GlobalTheory.CompanionTheory.RgExhHecke.rankOne | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.rankOne <;> assumption)
