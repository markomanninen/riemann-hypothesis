module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finite_places : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  first | exact @GlobalTheory.CompanionTheory.RatFinG.ratFin | exact GlobalTheory.CompanionTheory.RatFinG.ratFin | (intros; apply GlobalTheory.CompanionTheory.RatFinG.ratFin <;> assumption)
