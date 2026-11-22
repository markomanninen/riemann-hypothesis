module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_doubleLift_additive : ∀ D : D7, GlobalTheory.FinPl.SeeSmall D := by
  first | exact @GlobalTheory.SeeSmallPf.seeSmall | exact GlobalTheory.SeeSmallPf.seeSmall | (intros; apply GlobalTheory.SeeSmallPf.seeSmall <;> assumption)
