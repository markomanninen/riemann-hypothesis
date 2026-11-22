module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_euler_product_of : PositivityTheory.Rg.BcB.G8.Fin.EulerFinOf' := by
  first | exact @GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | exact GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | (intros; apply GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' <;> assumption)
