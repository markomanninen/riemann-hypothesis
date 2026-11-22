module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_determinant_law : PositivityTheory.RgEis.BdetLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.bdetLaw | exact GlobalTheory.CompanionTheory.RgEis.bdetLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.bdetLaw <;> assumption)
