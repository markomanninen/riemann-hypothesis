module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_restriction_rowOperators : GlobalTheory.LeviCut.ResDer := by
  first | exact @GlobalTheory.LeviCut.dualWeyl_resDer | exact GlobalTheory.LeviCut.dualWeyl_resDer | (intros; apply GlobalTheory.LeviCut.dualWeyl_resDer <;> assumption)
