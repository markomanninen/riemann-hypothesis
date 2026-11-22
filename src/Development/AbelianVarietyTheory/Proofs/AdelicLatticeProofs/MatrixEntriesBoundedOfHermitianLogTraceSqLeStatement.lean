module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixEntriesBoundedOfHermitianLogTraceSqLe
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  first | exact @GlobalTheory.ClassFin.entries_le_of_energy_le | exact GlobalTheory.ClassFin.entries_le_of_energy_le | (intros; apply GlobalTheory.ClassFin.entries_le_of_energy_le <;> assumption)
