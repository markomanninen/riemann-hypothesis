module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterLevelFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | exact GlobalTheory.CompanionTheory.GunrLev.psiLev_holds | (intros; apply GlobalTheory.CompanionTheory.GunrLev.psiLev_holds <;> assumption)
