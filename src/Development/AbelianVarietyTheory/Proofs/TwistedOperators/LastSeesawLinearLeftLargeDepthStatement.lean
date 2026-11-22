module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin

@[expose] public section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesaw_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  first | exact @GlobalTheory.LastPositionLin.lastLin_zero | exact GlobalTheory.LastPositionLin.lastLin_zero | (intros; apply GlobalTheory.LastPositionLin.lastLin_zero <;> assumption)
