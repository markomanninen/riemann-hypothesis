module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_test_function_exists : PositivityTheory.RgEis.TestSph := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTestSph.testSph | exact GlobalTheory.CompanionTheory.RgEisTestSph.testSph | (intros; apply GlobalTheory.CompanionTheory.RgEisTestSph.testSph <;> assumption)
