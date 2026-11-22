module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hypotheses_hold : PositivityTheory.Rg.BcB.G8.Fin.LocHyp := by
  first | exact @GlobalTheory.CompanionTheory.LocHypProof.locHyp | exact GlobalTheory.CompanionTheory.LocHypProof.locHyp | (intros; apply GlobalTheory.CompanionTheory.LocHypProof.locHyp <;> assumption)
