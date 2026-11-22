module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all : ∀ D : D7, GlobalTheory.FinPl.SuppFirst D := by
  first | exact @GlobalTheory.FinPl.suppFirst_all | exact GlobalTheory.FinPl.suppFirst_all | (intros; apply GlobalTheory.FinPl.suppFirst_all <;> assumption)
