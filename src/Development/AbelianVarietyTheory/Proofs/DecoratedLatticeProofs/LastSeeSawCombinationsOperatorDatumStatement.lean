module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_combinations_operatorDatum : ∀ D : D7, GlobalTheory.FinPl.LastOp D := by
  first | exact @GlobalTheory.LastOpPf.lastOp | exact GlobalTheory.LastOpPf.lastOp | (intros; apply GlobalTheory.LastOpPf.lastOp <;> assumption)
