module

public import Mathlib

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

section Basics

variable {G : Type*} [Group G]

variable [Fintype G]

end Basics

section IndFunMore

variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']

end IndFunMore

section Conj

variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]

def conjNormal (g : G) : A ≃* A where
  toFun a := ⟨g⁻¹ * a * g, by simpa using hA.conj_mem a a.2 g⁻¹⟩
  invFun a := ⟨g * a * g⁻¹, hA.conj_mem a a.2 g⟩
  left_inv a := by
    ext
    simp [mul_assoc]
  right_inv a := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

theorem conjNormal_mul (g h : G) (a : A) :
    conjNormal A (g * h) a = conjNormal A h (conjNormal A g a) := by
  apply Subtype.ext
  change (g * h)⁻¹ * (a : G) * (g * h) = h⁻¹ * (g⁻¹ * (a : G) * g) * h
  simp [mul_assoc]

theorem conjNormal_one (a : A) : conjNormal A 1 a = a := by
  apply Subtype.ext
  change (1 : G)⁻¹ * (a : G) * 1 = (a : G)
  simp

def inertia (θ : A → ℂ) : Subgroup G where
  carrier := {g | ∀ a, θ (conjNormal A g a) = θ a}
  one_mem' := by
    intro a
    rw [conjNormal_one]
  mul_mem' {g h} hg hh := by
    intro a
    rw [conjNormal_mul, hh, hg]
  inv_mem' {g} hg := by
    intro a
    calc θ (conjNormal A g⁻¹ a) = θ (conjNormal A g (conjNormal A g⁻¹ a)) := (hg _).symm
      _ = θ a := by rw [← conjNormal_mul, inv_mul_cancel, conjNormal_one]


end Conj

section Clifford

variable {G : Type*} [Group G] [Fintype G] {A : Subgroup G} [A.Normal]


end Clifford

end GroundTheory.LocalField
