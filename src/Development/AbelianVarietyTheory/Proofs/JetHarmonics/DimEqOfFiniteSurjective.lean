module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.CMObjBundlePull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RosatiAdjIffLamEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingHomExtRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrime
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.LamCM Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

namespace GlobalTheory.CMClaims

theorem laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
theorem secTwist : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
theorem homExt : CM.HomExtDvr := fun T K _ _ _ _ _ _ G G' _ _ hG hG' φ hφ =>
  GlobalTheory.existsUnique_hom_extension_semiAbelian T K G G' hG hG' φ hφ

section Vec

variable {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {G : Over (Sp R)} {G' : Over (Sp R')} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

variable (h : IsGrpPullback G' G (spMap f) φ)

variable [IsCommMonObj G'] {n : ℕ} {v : Fin n → (epsR R' ⟶ G')} (hv : IsLieBasis v)

end Vec

section Pair

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E}

end Pair

section Isog

theorem card_torsion_eq {M N : Type} [CommGroup M] [CommGroup N] (F : M →* N) (hF : Function.Surjective F) (m : ℕ)
    (hm : ∀ x, F x = 1 → x ^ (m + 1) = 1) :
    Nat.card {x : M // x ^ (m + 2) = 1} = Nat.card {y : N // y ^ (m + 2) = 1} := by
  refine Nat.card_eq_of_bijective (fun x => ⟨F x.1, by rw [← map_pow, x.2, map_one]⟩) ⟨fun a b e => ?_, fun y => ?_⟩
  · have e₁ : F (a.1 / b.1) = 1 := by rw [map_div, div_eq_one]; exact congrArg Subtype.val e
    have e₂ : (a.1 / b.1) ^ (m + 2) = 1 := by rw [div_pow, a.2, b.2, div_one]
    rw [pow_succ, hm _ e₁, _root_.one_mul, div_eq_one] at e₂
    exact Subtype.ext e₂
  · obtain ⟨x, hx⟩ := hF y.1
    have e₁ : (x ^ (m + 2)) ^ (m + 1) = 1 := hm _ (by rw [map_pow, hx, y.2])
    refine ⟨⟨x ^ ((m + 1) * (m + 1)), ?_⟩, Subtype.ext ?_⟩
    · rw [← pow_mul, show (m + 1) * (m + 1) * (m + 2) = (m + 2) * (m + 1) * (m + 1) by ring, pow_mul, pow_mul, e₁, one_pow]
    · change F _ = y.1
      rw [map_pow, hx, show (m + 1) * (m + 1) = (m + 2) * m + 1 by ring, pow_succ, pow_mul, y.2, one_pow, _root_.one_mul]

variable {K : Type} [Field K] [NumberField K]

theorem onto_points {R k : Type} [CommRing R] [Field k] [IsAlgClosed k] {P Q : Over (Sp R)} (Φ : P ⟶ Q)
    [IsFinite Φ.left] [Surjective Φ.left] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ Q) : ∃ x : Over.mk t ⟶ P, y = x ≫ Φ := by
  obtain ⟨p, hp⟩ := GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end Isog

section Sum

variable {K : Type} [Field K] [NumberField K]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l} {p q : ℕ}

end Sum

section Types

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

variable {E : Type} [Field E] [NumberField E]

end Types

section Lines

variable {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K} {φ : x.P.A.left ⟶ A.A.left}

end Lines

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable [StarRing (𝓞 E)] {l : Level H} {c : Coeff l} {p q : ℕ}

def Readable (o : abelian₂.LamObj c p q) : Prop :=
  abelian₂.IsFibreOf o.AΨ o.xΨ (abelian₂.gmap o.K₁) o.φΨg ∧ abelian₂.IsFibreOf o.A' o.x' (abelian₂.gmap o.K₁) o.φ'g ∧
    (∀ i, IsMonHom (o.φΨ i)) ∧ (∀ i, IsMonHom (o.φ' i)) ∧
    (∀ i (a : 𝓞 E), o.oaΨ.act a ≫ o.φΨ i = o.φΨ i ≫ o.oa.act a) ∧
    ∀ i (a : 𝓞 E), o.oa'.act a ≫ o.φ' i = o.φ' i ≫ o.oa.act a

variable (hs : ∀ a : 𝓞 E, star a = H.bar a) (o : abelian₂.LamObj c p q) (h : Readable o)

end Main

end GlobalTheory.CMClaims
