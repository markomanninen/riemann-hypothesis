module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_level_facts : PositivityTheory.Rg.BcB.G8.FinLevel := by
  first | exact @GlobalTheory.CompanionTheory.FinLevelTw.finLevel | exact GlobalTheory.CompanionTheory.FinLevelTw.finLevel | (intros; apply GlobalTheory.CompanionTheory.FinLevelTw.finLevel <;> assumption)
