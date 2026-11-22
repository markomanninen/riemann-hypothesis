module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit : ActSt → UnitSt → FrameSt := by
  first | exact @GlobalTheory.IsoTriv.frameSt_of | exact GlobalTheory.IsoTriv.frameSt_of | (intros; apply GlobalTheory.IsoTriv.frameSt_of <;> assumption)
