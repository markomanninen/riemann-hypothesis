module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof : InvDerSt := by
  first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)
