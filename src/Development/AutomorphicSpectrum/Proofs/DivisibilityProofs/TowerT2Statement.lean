module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T2 : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (K C' rd Lval : ℝ), 0 ≤ K → 0 ≤ C' → 1 ≤ rd → T.Proportional → FrobShape frob → I9 (Ψ := Ψ) (N := N) hh → T.Prop6 II frob → T.ThmBA II hh → T.PropF II C' rd Lval → T.LowerBoundAtBase II hh frob K rd Lval → T.T2 II (K + C' + 2) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.tower_T2_of_inputs <;> assumption)
