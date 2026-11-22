module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactNormBoundedBesselClosedSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)), IsClosedSub k r S → ∀ R : ℝ, IsCompact {g | g ∈ S ∧ opn g ≤ R} := by
  first | exact @GlobalTheory.SgInf.isCompact_normBounded | exact GlobalTheory.SgInf.isCompact_normBounded | (intros; apply GlobalTheory.SgInf.isCompact_normBounded <;> assumption)
