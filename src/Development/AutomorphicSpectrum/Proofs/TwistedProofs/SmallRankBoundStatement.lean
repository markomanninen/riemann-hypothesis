module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
