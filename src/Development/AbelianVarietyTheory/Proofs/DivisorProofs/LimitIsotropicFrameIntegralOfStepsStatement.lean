module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitIsotropicFrameIntegral_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  first | exact @GlobalTheory.IsoTriv.limFrame | exact GlobalTheory.IsoTriv.limFrame | (intros; apply GlobalTheory.IsoTriv.limFrame <;> assumption)
