module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  first | exact @GlobalTheory.FinPl.liftExact | exact GlobalTheory.FinPl.liftExact | (intros; apply GlobalTheory.FinPl.liftExact <;> assumption)
