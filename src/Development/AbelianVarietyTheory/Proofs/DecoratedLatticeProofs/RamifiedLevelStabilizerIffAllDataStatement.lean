module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SOnCols

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedLevel_stabilizer_iff_all_data : ∀ D : D7, GlobalTheory.SeeSaw.RamIff D := by
  first | exact @GlobalTheory.SeeSaw.ramIff_all | exact GlobalTheory.SeeSaw.ramIff_all | (intros; apply GlobalTheory.SeeSaw.ramIff_all <;> assumption)
