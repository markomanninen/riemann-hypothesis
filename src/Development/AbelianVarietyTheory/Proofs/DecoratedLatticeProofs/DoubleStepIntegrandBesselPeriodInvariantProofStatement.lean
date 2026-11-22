module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  first | exact @GlobalTheory.FinPl.HandInvPf.handInv | exact GlobalTheory.FinPl.HandInvPf.handInv | (intros; apply GlobalTheory.FinPl.HandInvPf.handInv <;> assumption)
