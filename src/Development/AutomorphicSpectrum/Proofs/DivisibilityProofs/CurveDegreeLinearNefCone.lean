module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.WeilBound.CoreStatements.FlagImmersions.RootCoefWeightedSumSplit

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem curveDeg_linear_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) :=
  @RootFieldNumerics.curveDeg_linear_and_nef

end GlobalTheory.CompanionTheory.Ar.Top
