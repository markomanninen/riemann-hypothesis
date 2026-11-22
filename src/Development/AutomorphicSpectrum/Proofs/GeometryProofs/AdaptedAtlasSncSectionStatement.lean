module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
public import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVariety
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA

@[expose] public section

open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_atlas_snc_section : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | exact GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas <;> assumption)
