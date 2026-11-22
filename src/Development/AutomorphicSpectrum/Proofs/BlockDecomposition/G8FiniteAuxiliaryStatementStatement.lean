module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_21 : PositivityTheory.Rg.BcB.G8.Fin.Regroup := by
  first | exact @GlobalTheory.CompanionTheory.RegroupFin.regroup | exact GlobalTheory.CompanionTheory.RegroupFin.regroup | (intros; apply GlobalTheory.CompanionTheory.RegroupFin.regroup <;> assumption)
