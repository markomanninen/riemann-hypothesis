module

public import Mathlib

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem mem_ideal_smul_top_iff_mem {V : Type} [CommRing V] (I : Ideal V) (x : V) :
    x ∈ I • (⊤ : Submodule V V) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem localHom_map_mem_maximalIdeal_pow {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) {x : A}
    (hx : x ∈ maximalIdeal A ^ n) : α x ∈ maximalIdeal V ^ n := by
  have h1 : (maximalIdeal A).map α ≤ maximalIdeal V := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    exact map_nonunit α y hy
  have := Ideal.mem_map_of_mem α hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 n this

theorem eval_map_mem_maximalIdeal_pow_of_coeff_mem {A V : Type} [CommRing A] [IsLocalRing A] [CommRing V]
    [IsLocalRing V] (α : A →+* V) [IsLocalHom α] (n : ℕ) (D : Polynomial A)
    (hD : ∀ i, D.coeff i ∈ maximalIdeal A ^ n) (η : V) :
    (D.map α).eval η ∈ maximalIdeal V ^ n := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (localHom_map_mem_maximalIdeal_pow α n (hD i))

end GlobalTheory
