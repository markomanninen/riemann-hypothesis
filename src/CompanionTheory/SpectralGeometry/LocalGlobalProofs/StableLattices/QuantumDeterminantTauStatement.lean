module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTau
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.GlRelTau

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantTau : CompanionTheory.RgExh.Hk.QdetTau := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | exact GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | (intros; apply GlobalTheory.CompanionTheory.CapelliTwist.qdetTau <;> assumption)
