module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_total : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | exact GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal <;> assumption)
