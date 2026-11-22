module

public import Mathlib

@[expose] public section

namespace GlobalTheory.ConjugationEquiv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjEquiv (N : Subgroup G) (b : G) (hb : ∀ u : G, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N where
  toFun u := ⟨b * (u : G) * b⁻¹, (hb u).1 u.2⟩
  invFun u := ⟨b⁻¹ * (u : G) * b, (hb _).2 (by
    have h : b * (b⁻¹ * (u : G) * b) * b⁻¹ = u := by group
    rw [h]; exact u.2)⟩
  left_inv u := Subtype.ext (by
    show b⁻¹ * (b * (u : G) * b⁻¹) * b = u
    group)
  right_inv u := Subtype.ext (by
    show b * (b⁻¹ * (u : G) * b) * b⁻¹ = u
    group)
  map_mul' u v := Subtype.ext (by
    show b * ((u : G) * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹)
    group)
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end GlobalTheory.ConjugationEquiv
