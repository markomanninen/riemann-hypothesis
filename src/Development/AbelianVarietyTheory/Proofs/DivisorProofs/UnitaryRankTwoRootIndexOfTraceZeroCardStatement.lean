module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCard
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  first | exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | exact GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | (intros; apply GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex <;> assumption)
