module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_invariance_of_rank_one_two : GlobalTheory.LeviCut.RankOne → GlobalTheory.LeviCut.RankTwo → GlobalTheory.LeviCut.GridInv := by
  first | exact @GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | exact GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | (intros; apply GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo <;> assumption)
