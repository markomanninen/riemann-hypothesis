module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs <;> assumption)
