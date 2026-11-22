module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MaximalCompactStatement : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  first | exact @GlobalTheory.CompanionTheory.RgKMaj.kMaj | exact GlobalTheory.CompanionTheory.RgKMaj.kMaj | (intros; apply GlobalTheory.CompanionTheory.RgKMaj.kMaj <;> assumption)
