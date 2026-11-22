module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)
