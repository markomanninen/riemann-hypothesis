module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuples
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_levelPrime_law_all_tuples : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  first | exact @GlobalTheory.LevPrimeAll.lawLevelPrime_all | exact GlobalTheory.LevPrimeAll.lawLevelPrime_all | (intros; apply GlobalTheory.LevPrimeAll.lawLevelPrime_all <;> assumption)
