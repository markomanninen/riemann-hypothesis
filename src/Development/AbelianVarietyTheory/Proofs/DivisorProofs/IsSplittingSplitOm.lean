module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))


variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




def dblNum (σ : κ ≃ α × β) : κ ⊕ κ ≃ α × (β ⊕ β) := (σ.sumCongr σ).trans (Equiv.prodSumDistrib α β β).symm

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_fromCols (σ : κ ≃ α × β) (X Y : Matrix α β R) :
    flat (dblNum σ) (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := by
  funext k
  cases k <;> rfl

end GlobalTheory.WeilM

end
