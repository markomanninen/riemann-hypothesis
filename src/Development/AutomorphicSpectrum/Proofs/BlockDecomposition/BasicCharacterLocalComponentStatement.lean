module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicCharacterLocalComponent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basic_character_unramified : PositivityTheory.SiegelWeilFormula.Gunr.PsiBasic := by
  first | exact @GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | exact GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic | (intros; apply GlobalTheory.CompanionTheory.AdelicCharLocal.psiBasic <;> assumption)
