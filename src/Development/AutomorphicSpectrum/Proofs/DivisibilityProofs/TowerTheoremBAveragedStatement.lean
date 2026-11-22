module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveraged
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B_averaged : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II → LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | exact GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA <;> assumption)
