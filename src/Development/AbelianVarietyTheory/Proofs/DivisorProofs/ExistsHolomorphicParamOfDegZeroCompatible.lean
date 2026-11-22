module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZeroStatement

@[expose] public section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (K.sh (K.le_refl k) (a k)) := hG _ _ (ptHom (K.jet k) (K.le_refl k)) rfl
    let j : K.Hom (K.triv k) (K.jet k) :=
      fromTriv (K.jet k) (K.le_refl k) (tszeSec dw)
        (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
        (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
          fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
            simp only [RingHom.comp_apply, sh_refl]
            exact tsze_expand h fun a ↦ dw a h⟩)
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ j rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (K.sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
