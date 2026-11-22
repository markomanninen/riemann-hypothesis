module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitAlmostEverywhereFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_almost_everywhere_facts : PositivityTheory.Rg.BcB.G8.Fin.UnitAE := by
  first | exact @GlobalTheory.CompanionTheory.UnitAEPair.main | exact GlobalTheory.CompanionTheory.UnitAEPair.main | (intros; apply GlobalTheory.CompanionTheory.UnitAEPair.main <;> assumption)
