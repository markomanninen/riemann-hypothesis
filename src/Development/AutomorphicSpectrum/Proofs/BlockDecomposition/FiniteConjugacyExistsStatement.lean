module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_conjugacy_exists : PositivityTheory.Rg.BcB.G8.Fin.CjEx := by
  first | exact @GlobalTheory.CompanionTheory.CjEx.cjEx | exact GlobalTheory.CompanionTheory.CjEx.cjEx | (intros; apply GlobalTheory.CompanionTheory.CjEx.cjEx <;> assumption)
