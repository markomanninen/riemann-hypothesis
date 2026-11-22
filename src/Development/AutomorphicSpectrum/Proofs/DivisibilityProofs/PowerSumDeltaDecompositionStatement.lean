module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumDeltaDecomposition
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sum_delta_decomposition : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ), j ≤ N → 0 < N → FrobShape frob → ∃ κ : ℕ → ℝ, ∀ (p : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), 2 ≤ p → 1 ≤ k → deltaTerm j p τ (frob p τ) k Q = -(Real.log p / ((p : ℝ) - 1)) * ∑ σ, Sh j σ (pk τ k * Q) + κ p * ∑ σ, Tot σ (pk τ k * Q) + restTerm j p (frob p τ) k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.deltaTerm_eq | exact GlobalTheory.CompanionTheory.Ar.Top.deltaTerm_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.deltaTerm_eq <;> assumption)
