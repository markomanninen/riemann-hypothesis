module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFibres
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeSurjectiveOfOntoComplexPoints
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

end Partner

section Metric

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

end Metric

section Embeddings

end Embeddings

section Isogeny

end Isogeny

section Object

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

end Object

end GlobalTheory.CMSharedCompare
