module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
