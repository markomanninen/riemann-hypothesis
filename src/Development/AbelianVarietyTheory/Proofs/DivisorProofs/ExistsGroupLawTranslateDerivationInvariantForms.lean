module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapOfSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let T := Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1
  let σ : Sec A.hom V.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeRight
  let τ : Sec A.hom U.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeLeft
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : Over.mk (spMap (algebraMap R (Sec A.hom V.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p := GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ := GlobalTheory.DeRham.spOver τ ≫ aU
  let y₀ := GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let dualInclusion := TrivSqZeroExt.inlAlgHom R T T
  let dualProjection := TrivSqZeroExt.fstHom R T T
  let q := GlobalTheory.DeRham.spOver dualInclusion ≫ q'
  let red := GlobalTheory.DeRham.spOver dualProjection
  have h1 : red ≫ p = y₀ := by
    have hφ : dualProjection.comp φ = σ := AlgHom.ext fun c ↦ fst_semiDerHom σ θ hθ' c
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hφ]
  have h2 : red ≫ q = q' := by
    have hsection : dualProjection.comp dualInclusion = AlgHom.id R T := AlgHom.ext fun _ ↦ rfl
    have hid : GlobalTheory.DeRham.spOver (AlgHom.id R T) = 𝟙 (Over.mk (spMap (algebraMap R T))) := by
      apply Over.OverMorphism.ext
      simp only [GlobalTheory.DeRham.spOver, Over.homMk_left, Over.id_left]
      exact Cris.spMap_id T
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hsection, hid, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have h3Left : spMap dualProjection.toRingHom ≫ (p * q).left = spMap τ.toRingHom ≫ affPt A.hom U.unop := by
    simpa only [Over.comp_left, red, x₀, aU, GlobalTheory.DeRham.spOver, Over.homMk_left,
      AlgHom.toRingHom_eq_coe]
      using congrArg (fun f ↦ f.left) h3
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    have hsurj : Function.Surjective (spMap dualProjection.toRingHom) :=
      GlobalTheory.PtExt.surjective_spMap_of_sq _ TrivSqZeroExt.fst_surjective fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        ext <;> simp [ha']
    intro x _
    obtain ⟨t, rfl⟩ := hsurj x
    change ((spMap dualProjection.toRingHom ≫ (p * q).left).base t) ∈ U.unop.1
    rw [h3Left]
    change U.unop.2.fromSpec.base ((spMap τ.toRingHom).base t) ∈ U.unop.1
    exact (Set.ext_iff.mp U.unop.2.range_fromSpec _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber T)) := Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap ψ.toRingHom ≫ affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : dualProjection.toRingHom.comp ψ.toRingHom = τ.toRingHom := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact h3Left
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have hp : p.left = spMap φ.toRingHom ≫ affPt A.hom V.unop := by
    simp only [p, aV, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, AlgHom.toRingHom_eq_coe]
  have hq : q.left = spMap (algebraMap T (DualNumber T)) ≫ q'.left := by
    have hι : (dualInclusion : T →+* DualNumber T) = algebraMap T (DualNumber T) := RingHom.ext fun _ ↦ rfl
    simp only [q, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, hι]
  have key := w.2 T V.unop U.unop φ ψ p q q'.left hp hq hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
