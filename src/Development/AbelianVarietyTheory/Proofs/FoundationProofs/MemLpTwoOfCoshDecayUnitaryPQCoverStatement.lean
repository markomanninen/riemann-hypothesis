module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCover
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  first | exact @GlobalTheory.CoshSqInt.memLp_two_of_decay | exact GlobalTheory.CoshSqInt.memLp_two_of_decay | (intros; apply GlobalTheory.CoshSqInt.memLp_two_of_decay <;> assumption)
