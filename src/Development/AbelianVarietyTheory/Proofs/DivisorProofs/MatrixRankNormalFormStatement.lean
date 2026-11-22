module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan

@[expose] public section

open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K), H * X * Q = 1 := by
  first | exact @GlobalTheory.rank_frame_exists | exact GlobalTheory.rank_frame_exists | (intros; apply GlobalTheory.rank_frame_exists <;> assumption)
