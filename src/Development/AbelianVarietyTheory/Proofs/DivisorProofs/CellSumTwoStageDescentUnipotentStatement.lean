module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotent
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_sum_two_stage_descent_unipotent : GlobalTheory.SatakeWeyl.Descent := by
  first | exact @GlobalTheory.SatakeWeyl.descent | exact GlobalTheory.SatakeWeyl.descent | (intros; apply GlobalTheory.SatakeWeyl.descent <;> assumption)
