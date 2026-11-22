module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RemainderTermSummable
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.remainder_term_summable : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | exact GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.restTerm_bound_and_tendsto <;> assumption)
