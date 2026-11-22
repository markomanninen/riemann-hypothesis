module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaOperatorFrameSeries_of_steps : InvDerSt → LinSt → FrameSt → NabSt := by
  first | exact @GlobalTheory.IsoTriv.nabSt_of | exact GlobalTheory.IsoTriv.nabSt_of | (intros; apply GlobalTheory.IsoTriv.nabSt_of <;> assumption)
