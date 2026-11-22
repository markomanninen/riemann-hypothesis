module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackward
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeBackward : CompanionTheory.RgExh.Hk.Back := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | exact GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back <;> assumption)
