module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_of_average : SecLaw → AvgMem → Unfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisUnfold.unfold | exact GlobalTheory.CompanionTheory.RgEisUnfold.unfold | (intros; apply GlobalTheory.CompanionTheory.RgEisUnfold.unfold <;> assumption)
