module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_iff_point_ideal_le : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x y : MP ℤ m n), x ⤳ y ↔ ptIdeal x ≤ ptIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | exact GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | (intros; apply GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le <;> assumption)
