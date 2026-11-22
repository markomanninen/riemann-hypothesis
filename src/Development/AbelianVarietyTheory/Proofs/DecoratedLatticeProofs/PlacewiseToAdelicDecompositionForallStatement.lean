module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placewise_to_adelicDecomposition_forall : ∀ D : D7, GlobalTheory.FinPl.PlacesToAdeles D := by
  first | exact @GlobalTheory.FinPl.placesToAdeles_all | exact GlobalTheory.FinPl.placesToAdeles_all | (intros; apply GlobalTheory.FinPl.placesToAdeles_all <;> assumption)
