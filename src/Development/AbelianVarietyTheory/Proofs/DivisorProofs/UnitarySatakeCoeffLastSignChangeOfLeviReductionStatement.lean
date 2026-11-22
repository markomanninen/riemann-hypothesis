module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffLastSignChangeOfLeviReduction
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexTwo → GlobalTheory.SatakeWeyl.IndexThree → GlobalTheory.SatakeWeyl.CoeffNeg := by
  first | exact @GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep | exact GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep | (intros; apply GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep <;> assumption)
