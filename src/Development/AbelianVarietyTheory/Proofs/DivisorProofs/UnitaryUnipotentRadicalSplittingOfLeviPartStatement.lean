module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPart
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
