module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq : GlobalTheory.SatakeWeyl.IntIndex := by
  first | exact @GlobalTheory.SatakeWeyl.intIndex | exact GlobalTheory.SatakeWeyl.intIndex | (intros; apply GlobalTheory.SatakeWeyl.intIndex <;> assumption)
