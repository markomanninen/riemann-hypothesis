module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT1Limit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T1_limit : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs <;> assumption)
