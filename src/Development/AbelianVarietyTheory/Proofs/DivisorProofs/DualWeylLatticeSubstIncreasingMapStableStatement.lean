module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable : GlobalTheory.LeviCut.SubstMem := by
  first | exact @GlobalTheory.LeviCut.substMem | exact GlobalTheory.LeviCut.substMem | (intros; apply GlobalTheory.LeviCut.substMem <;> assumption)
