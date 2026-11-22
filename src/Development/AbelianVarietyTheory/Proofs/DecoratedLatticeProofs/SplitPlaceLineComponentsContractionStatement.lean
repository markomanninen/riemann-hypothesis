module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContraction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_lineComponents_contraction : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  first | exact @GlobalTheory.FinPl.contraction_all | exact GlobalTheory.FinPl.contraction_all | (intros; apply GlobalTheory.FinPl.contraction_all <;> assumption)
