module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTiedStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeftStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Field

variable {F : Type} [Field F]

end Field

variable {Ω : Type} [Field Ω]


theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

section Values

variable {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L} {c : ∀ k, ι k}

end Values

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Systems

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end Systems

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

end Clauses

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
