module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.VFormula

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem vFormula_of_classicalTheorems (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) :
    VLen D e + KStar.TotallyRealRoots.nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  have hfl := fun r (hr : 0 < r) => GlobalTheory.TateLimit.finite_level D e hP hc r hr
  have hcok := GlobalTheory.TateLimit.ptCokerAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have hsha := GlobalTheory.TateLimit.ptShaAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have length_add_coker {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X]
      [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
      Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
        Module.length R (LinearMap.ker f) + Module.length R Y := by
    have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]
  have h : Formalism.GaloisCohomology.VFormula := by
    intro F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc
    have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
      unfold localH2
      rw [LinearMap.ker_pi]
      rfl
    have key := length_add_coker (localH2 D e)
    rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
    unfold VLen sumLocalH0TwistLength
    rw [key]
    congr 1
    exact Finset.sum_congr rfl (fun v _ => hloc v)
  have h := h F Ω l D e hc hcok hsha (GlobalTheory.TateLimit.local_tate_duality_h2_limit hF hT D e)
  rwa [length_H0_global_eq_nu] at h

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

theorem VLen_le_shaLen_add (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) : VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_of_classicalTheorems hP hF hT hc]
  exact le_self_add

end

end UpperTheory.V.LDataCardLeFinrank

end
