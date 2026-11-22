module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

@[expose] public section

namespace GlobalTheory.TraceOnInjectiveMap

theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dite_eq_left (hpres.2 h'), dite_eq_left h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hpres.1 h'), dite_eq_right h']

end GlobalTheory.TraceOnInjectiveMap
