module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vectors_span_dense : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | exact GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan <;> assumption)
