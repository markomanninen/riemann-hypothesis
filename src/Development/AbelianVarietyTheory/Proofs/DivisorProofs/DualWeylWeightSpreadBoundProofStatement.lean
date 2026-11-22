module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  first | exact @GlobalTheory.LeviCut.nablaBdd | exact GlobalTheory.LeviCut.nablaBdd | (intros; apply GlobalTheory.LeviCut.nablaBdd <;> assumption)
