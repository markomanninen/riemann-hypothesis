module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTorusTranslatesCover
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torus_translates_cover : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus | exact GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartCover.mcPts_finite_cover_up_to_torus <;> assumption)
