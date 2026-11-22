module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  first | exact @GlobalTheory.FinPl.ramBijective_holds | exact GlobalTheory.FinPl.ramBijective_holds | (intros; apply GlobalTheory.FinPl.ramBijective_holds <;> assumption)
