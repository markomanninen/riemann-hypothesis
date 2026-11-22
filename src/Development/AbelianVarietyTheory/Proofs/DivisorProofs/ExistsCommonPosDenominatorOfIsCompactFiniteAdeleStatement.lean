module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdele
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  first | (exact @GlobalTheory.AfPCpctDen.main) | (exact GlobalTheory.AfPCpctDen.main) | (intros; apply GlobalTheory.AfPCpctDen.main  <;> assumption)
