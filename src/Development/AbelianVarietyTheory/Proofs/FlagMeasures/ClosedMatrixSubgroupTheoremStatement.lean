module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_matrix_subgroup_theorem : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.ClosedMatGroup.closed_subgroup | exact GlobalTheory.ClosedMatGroup.closed_subgroup | (intros; apply GlobalTheory.ClosedMatGroup.closed_subgroup <;> assumption)
