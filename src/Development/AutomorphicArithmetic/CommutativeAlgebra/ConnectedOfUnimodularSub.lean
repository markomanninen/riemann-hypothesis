module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem cond2 (p : ℕ) (T : Scheme.{0}) (a b : Sx (CN (L1 D d)) p T)
    (h : sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a =
      sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) b) :
    EtLoc T fun V k => sxRes k a = sxRes k b ∨ ∃ u : Sx (CN (L2 D d)) p V,
      sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u =
        sxRes k (sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a) := by
  have hab : a = b := by
    let a' : Sm (L1 D d) p T := a
    let b' : Sm (L1 D d) p T := b
    have h' : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    exact Subtype.ext (funext fun i => Subtype.ext (h' i))
  exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V k _ => Or.inl (by rw [hab])⟩

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory
