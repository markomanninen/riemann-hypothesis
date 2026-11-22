module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
      (g : T ⟶ Spec (CommRingCat.of A))
      (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
      (U V : T.affineOpens) (h : (U : T.Opens) ≤ V),
      letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
      ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
        (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
          (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤
        RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  intro A B _ _ _ T g I U V h
  let := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  let := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
          (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op) }
  refine ⟨ρ, rfl, ?_⟩
  have kappa_tmul (W : T.Opens) (c : Γ(T, W)) (b : B) :
      letI := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
      GlobalTheory.HilbAff.kappa A B g I W (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd _ g).app W).hom c *
          ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) (by simp)).hom
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
    let := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
    let : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) :=
      (((I.subschemeι ≫ pullback.snd _ g).app W).hom.comp
        (GlobalTheory.HilbAff.secAlg A g W)).toAlgebra
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hκ (t : Γ(T, V) ⊗[A] B) :
      GlobalTheory.HilbAff.kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (GlobalTheory.HilbAff.kappa A B g I V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
      have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := rfl
      rw [hc]
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
        rfl
      · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
            (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
            (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
        exact (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [hκ t, ht, map_zero]
