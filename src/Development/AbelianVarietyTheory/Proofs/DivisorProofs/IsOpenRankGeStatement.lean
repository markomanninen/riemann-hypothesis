module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRankGe
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan

@[expose] public section

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_rank_ge : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  first | exact @GlobalTheory.isOpen_setOf_le_rank_localField | exact GlobalTheory.isOpen_setOf_le_rank_localField | (intros; apply GlobalTheory.isOpen_setOf_le_rank_localField <;> assumption)
