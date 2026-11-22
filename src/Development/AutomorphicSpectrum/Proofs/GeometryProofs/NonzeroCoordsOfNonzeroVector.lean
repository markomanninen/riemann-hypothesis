module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameZero

theorem tmul_one_injective {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Projective (𝓞 L) M] (x : M)
    (h : (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x = 0) : x = 0 := by
  have hinj : Function.Injective (Algebra.linearMap (𝓞 L) (ComplexAt σ)) := by
    intro a b hab
    have h1 : σ (a : L) = σ (b : L) := hab
    exact RingOfIntegers.coe_injective (σ.injective h1)
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  have h2 : (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M ((1 : 𝓞 L) ⊗ₜ[𝓞 L] x) =
      (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, Algebra.linearMap_apply, map_one, h]
  have h3 := hr h2
  have h4 := congrArg (TensorProduct.lid (𝓞 L) M) h3
  simpa using h4

theorem core_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (C : InnerProductSpace.Core ℂ V)
    (v : V) (h : (C.inner v v : ℂ).re = 0) : v = 0 := by
  apply C.definite
  have him : (C.inner v v : ℂ).im = 0 := by
    have h1 := C.conj_inner_symm v v
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    linarith
  exact Complex.ext h him

theorem coord_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier)
    (c : Fin D.g → ℂ) (hlen : D.len σ x ^ 2 = Real.pi * (a.herm c c).re) (hx : x ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hx
  have hherm : a.herm 0 0 = 0 := by simp [ArchFrame.herm]
  rw [hherm, Complex.zero_re, mul_zero] at hlen
  have hl : D.len σ x = 0 := by simpa using hlen
  have hnn : 0 ≤ (((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ)).re :=
    (D.B.metric.form σ).re_inner_nonneg _
  have hle := Real.sqrt_eq_zero'.mp hl
  exact tmul_one_injective σ D.B.carrier x (core_eq_zero _ _ (le_antisymm hle hnn))

end GlobalTheory.CompanionTheory.Ar.Sl.FrameZero
