module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.WeilBound.CoreStatements.FlagImmersions.PolarizationCoefficientsBound

@[expose] public section

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem polarisation_functional : ∀ (J : Type) [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ), ∃ Pl : MvPolynomial J ℝ, Pl.IsHomogeneous d ∧ (∀ c : J → ℝ, eval c Pl = Φ ((-∑ x, C (c x) * X x) ^ d)) ∧ (∀ m : J →₀ ℕ, m.degree = d → AddMonoidAlgebra.coeff Pl m = (-1) ^ d * (m.multinomial : ℝ) * Φ (monomial m 1)) ∧ ∀ m : J →₀ ℕ, m.degree = d → |Φ (monomial m 1)| ≤ |Pl.coeff m| :=
  @RootFieldNumerics.polarization_coefficients_bound

end GlobalTheory.CompanionTheory.Ar.Top
