module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_generic_fibre_of_snc : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y e bd → SmoothGenericFibreM y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel <;> assumption)
