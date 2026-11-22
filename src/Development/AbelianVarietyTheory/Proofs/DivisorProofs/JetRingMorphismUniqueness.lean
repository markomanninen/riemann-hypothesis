module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

end BC

end GlobalTheory.JetIsotropic
