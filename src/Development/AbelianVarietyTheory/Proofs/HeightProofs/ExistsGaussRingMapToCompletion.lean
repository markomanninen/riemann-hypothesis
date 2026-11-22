module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.GaussRingCompletionRename

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.GaussCompletion

open ReciprocityTheory.ChartRestriction.G

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussCompletionOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussCompletionOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussCompletionKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussCompletionKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra

theorem exists_gaussRing_map :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) := by
  intro D B P j X la N D' N' σ
  let : Algebra (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) :=
    ((algebraMap (Pol X la N) (Op X la N)).comp
      (MvPolynomial.renameEquiv (X.Ol la) σ).toRingEquiv.toRingHom).toAlgebra
  have halg (p : MvPolynomial (T0.TVar D' N') (X.Ol la)) :
      algebraMap (MvPolynomial (T0.TVar D' N') (X.Ol la)) (Op X la N) p =
        algebraMap (Pol X la N) (Op X la N) (MvPolynomial.rename σ p) := rfl
  let Q := Formalism.DV.gaussIdeal (T0.TVar D' N') (X.Ol la)
  have : Q.IsPrime :=
    Formalism.DV.GaussP.gaussIdeal_isPrime (T0.TVar D' N') (X.Ol la)
  have : IsLocalization.AtPrime (Op X la N) Q :=
    isLocalization_rename (IsLocalRing.maximalIdeal (X.Ol la)) σ (gI X la N) rfl Q rfl
  obtain ⟨-, f, hf, hflat, hlocal, hmax, hres⟩ :=
    GlobalTheory.gaussRing_completion B.KO D' N' la (X.Ol la)
      (algebraMap_injective la) (map_asIdeal la) (exists_sub_mem la) Q rfl (Op X la N)
  have hinj : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective _ (gI X la N).primeCompl_le_nonZeroDivisors
  have hfinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (T0.laT D' N' la).primeCompl x
    have hzero := congrArg f h
    rw [map_mul, hx, zero_mul, hf, halg] at hzero
    have hp : p = 0 := by
      have hrename := hinj (hzero.symm.trans (map_zero _).symm)
      have hmap := MvPolynomial.rename_injective σ σ.injective (hrename.trans (map_zero _).symm)
      exact MvPolynomial.map_injective _ (algebraMap_injective la) (hmap.trans (map_zero _).symm)
    simp only [hp, map_zero] at h
    exact (IsLocalization.map_units (T0.Op D' N' la) s).mul_left_eq_zero.mp h
  let := T0.algOpKT (K := B.KO) D' N' la
  have := T0.isFractionRing_Op (K := B.KO) D' N' la
  let ι : Op X la N →+* Kp X la N := algebraMap (Op X la N) (FractionRing (Op X la N))
  have hg : Function.Injective (ι.comp f) :=
    (IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp hfinj
  let φ : T0.KTf B.KO D' N' →+* Kp X la N :=
    IsFractionRing.lift (A := T0.Op D' N' la) hg
  have hφ (o : T0.Op D' N' la) : φ (T0.OpToKT D' N' la o) = ι (f o) :=
    IsFractionRing.lift_algebraMap (A := T0.Op D' N' la) hg o
  have hφp (p : T0.OT B.KO D' N') :
      φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N')
        (MvPolynomial.map (algebraMap (𝓞 B.KO) B.KO) p)) =
      ι (algebraMap (Pol X la N) (Op X la N)
        (MvPolynomial.rename σ (MvPolynomial.map (algebraMap (𝓞 B.KO) (X.Ol la)) p))) := by
    rw [← halg, ← hf, ← hφ, T0.OpToKT, IsLocalization.lift_eq]
    rfl
  refine ⟨f, φ, hflat, hlocal, hmax, hres, hφ, ?_, ?_⟩
  · have hconst : φ.comp (algebraMap B.KO (T0.KTf B.KO D' N')) =
        (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)) := by
      refine IsFractionRing.ringHom_ext (A := 𝓞 B.KO) fun a => ?_
      have h := hφp (MvPolynomial.C a)
      rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.rename_C] at h
      simp only [RingHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply B.KO (T0.KTp B.KO D' N') (T0.KTf B.KO D' N'),
        MvPolynomial.algebraMap_eq, h, ← Formalism.MainNotions.Gaps.LocalGlobalPassage.coe_algO]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la) _
          (algebraMap (X.Ol la) (X.Kl la) (algebraMap (𝓞 B.KO) (X.Ol la) a)) : FractionRing (Op X la N))
      rw [IsFractionRing.lift_algebraMap]
      change ι (algebraMap (Pol X la N) (Op X la N)
          (MvPolynomial.C (algebraMap (𝓞 B.KO) (X.Ol la) a))) =
        ι (algebraMap (X.Ol la) (Op X la N) (algebraMap (𝓞 B.KO) (X.Ol la) a))
      rw [IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        MvPolynomial.algebraMap_eq]
    intro a
    exact DFunLike.congr_fun hconst a
  · intro q
    have h := hφp (MvPolynomial.X q)
    rw [MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.rename_X] at h
    exact h

end

end GlobalTheory.GaussCompletion
