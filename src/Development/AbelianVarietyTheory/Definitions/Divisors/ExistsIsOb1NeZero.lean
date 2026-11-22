module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.Model

section General

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}

variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)

include hI in
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rw [← pow_two, hI] at this
  simpa using this

variable {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]



include hI hs in
theorem exists_isSig (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (semi : SemiHom π p) (surj : Function.Surjective p)
    (ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) : ∃ σ, α.IsSig p σ := by
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have h0 : b - b' ∈ I.map (algebraMap R B) := (ker _).1 (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← smul_sub, Algebra.smul_def]
    exact mul_eq_zero_of_mem (map_sq hI B) (Ideal.mem_map_of_mem _ (α.mem y)) h0
  have e := Function.surjInv_eq surj
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b ↦ α.k y • Function.surjInv surj b)
    fun b b' ↦ by rw [← smul_add]; exact key _ _ _ (by rw [map_add (f := _), e, e, e])) fun y y' ↦ by
      ext b; simp [add_smul]
  refine ⟨TensorProduct.liftAddHom f fun r y b ↦ ?_, fun y b ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := hs r
    change α.k (π r • y) • Function.surjInv surj b = α.k y • Function.surjInv surj (π r • b)
    rw [α.smul, mul_comm, mul_smul]
    exact key _ _ _ (by rw [semi, e, e])
  · exact key _ _ _ (e _)

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}



end General

section Unique

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]

variable {C C' : Type} [Category.{0} C] [Category.{0} C'] {F : C ⥤ CommAlgCat.{0} R₀} {F' : C' ⥤ CommAlgCat.{0} R₀}

end Unique

section Line

open Polynomial

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁]
variable (hI : I ^ 2 = 0) (hs : Function.Surjective π) (hk : RingHom.ker π = I)



variable {C : Type} [Category.{0} C]




end Line

end GlobalTheory.Obs.Model
