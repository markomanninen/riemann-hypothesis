module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntegerCoefficientsRational

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem clear_rat_weight_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j :=
  @RootFieldNumerics.exists_integer_coefficients_rational

end GlobalTheory.CompanionTheory.Ar.Top
