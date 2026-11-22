module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndex
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex : GlobalTheory.SatakeWeyl.UnimodFin → GlobalTheory.SatakeWeyl.Unimod := by
  first | exact @GlobalTheory.SatakeWeyl.unimod_of_unimodFin | exact GlobalTheory.SatakeWeyl.unimod_of_unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimod_of_unimodFin <;> assumption)
