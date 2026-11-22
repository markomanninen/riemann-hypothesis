module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_spherical_K : StdGood → BdetLaw → TestFun → TestK := by
  first | exact @GlobalTheory.CompanionTheory.EisTestK.testK | exact GlobalTheory.CompanionTheory.EisTestK.testK | (intros; apply GlobalTheory.CompanionTheory.EisTestK.testK <;> assumption)
