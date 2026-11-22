module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartVanishingSection
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_chart_vanishing_section : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s → IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N → ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧ Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧ ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt.exists_chart <;> assumption)
