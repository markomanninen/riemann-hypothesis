module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGap
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap | exact GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap <;> assumption)
