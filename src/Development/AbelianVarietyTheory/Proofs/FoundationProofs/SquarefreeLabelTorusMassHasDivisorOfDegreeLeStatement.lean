module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N → mass g N (HasDiv g a) ≤ 7 / 8 := by
  first | exact @GlobalTheory.BadShare.mass_hasDiv_le | exact GlobalTheory.BadShare.mass_hasDiv_le | (intros; apply GlobalTheory.BadShare.mass_hasDiv_le <;> assumption)
