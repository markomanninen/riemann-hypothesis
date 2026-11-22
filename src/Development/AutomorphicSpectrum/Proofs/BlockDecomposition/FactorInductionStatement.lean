module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_induction : GlobalTheory.CompanionTheory.EGlue.FactorStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.factorStep_holds | exact GlobalTheory.CompanionTheory.EGlue.factorStep_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.factorStep_holds <;> assumption)
