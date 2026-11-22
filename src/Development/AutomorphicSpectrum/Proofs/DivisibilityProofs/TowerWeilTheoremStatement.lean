module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheorem
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weil_theorem : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmW_tower | exact GlobalTheory.CompanionTheory.Ar.Top.thmW_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmW_tower <;> assumption)
