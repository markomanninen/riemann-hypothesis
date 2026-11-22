module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionIntegralPoint_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  first | exact @GlobalTheory.IsoTriv.limPt_of_steps | exact GlobalTheory.IsoTriv.limPt_of_steps | (intros; apply GlobalTheory.IsoTriv.limPt_of_steps <;> assumption)
