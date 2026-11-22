module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial

@[expose] public section

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyGeneric_of_keyClosedPts' : GlobalTheory.LocAcyc.KeyClosedPts → GlobalTheory.LocAcyc.KeyGeneric := by
  first | (exact @GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (exact GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts) | (intros; apply GlobalTheory.LocAcyc.keyGeneric_of_keyClosedPts  <;> assumption)
