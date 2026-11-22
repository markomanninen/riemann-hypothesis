module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRoots

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.skew_operator_bounded_by_polynomial_roots :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : M →ₗ[ℂ] H), Function.Injective ι → ∀ T : Module.End ℂ M,
      (∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) →
      ∀ m : Polynomial ℂ, m ≠ 0 → ∀ κ : ℝ, 0 ≤ κ → (∀ r ∈ m.roots, ‖r‖ ≤ κ) →
      ∀ x, Polynomial.aeval T m x = 0 → ‖ι (T x)‖ ≤ κ * ‖ι x‖ :=
  GlobalTheory.CompanionTheory.SkewSpec.norm_le_of_aeval_eq_zero
