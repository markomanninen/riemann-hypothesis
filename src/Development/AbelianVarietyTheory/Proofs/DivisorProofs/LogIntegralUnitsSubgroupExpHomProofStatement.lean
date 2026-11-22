module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof : UnitSt := by
  first | exact @GlobalTheory.IsoTriv.unitSt | exact GlobalTheory.IsoTriv.unitSt | (intros; apply GlobalTheory.IsoTriv.unitSt <;> assumption)
