module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.NormalizedMatrixSpan

@[reducible] noncomputable def Mat (C : Type) (N : ℕ) : Type := Matrix (Fin N) (Fin N) C

noncomputable def Normd {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Prop :=
  ∀ g : Γ, ∀ a ∈ A,
    (ρ g : Matrix (Fin N) (Fin N) C) * a * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) ∈ A

noncomputable def gens {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x : Mat C N | ∃ a ∈ A, ∃ g : Γ, x = a * (ρ g : Matrix (Fin N) (Fin N) C)}

theorem span_mul {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
    (A : Subalgebra C (Mat C N)) (hA : Normd ρ A) (x y : Mat C N)
    (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) := by
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]

end UpperTheory.Reformulated.B.NormalizedMatrixSpan
