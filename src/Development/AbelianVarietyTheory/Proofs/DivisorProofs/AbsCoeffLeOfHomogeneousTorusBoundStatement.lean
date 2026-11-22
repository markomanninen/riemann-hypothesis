module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsCoeffLeOfHomogeneousTorusBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_coeff_le_of_homogeneous_torus_bound : ∀ (D q : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ) (M : ℝ), T.IsHomogeneous q → (∀ z : Fin (D + 1) → ℂ, z 0 = 1 → (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M) → ∀ α, |((AddMonoidAlgebra.coeff T α : ℤ) : ℝ)| ≤ M := by
  first | exact @GlobalTheory.HSAmp.CoefTorus.coeff_le_of_torus_bound | exact GlobalTheory.HSAmp.CoefTorus.coeff_le_of_torus_bound | (intros; apply GlobalTheory.HSAmp.CoefTorus.coeff_le_of_torus_bound <;> assumption)
