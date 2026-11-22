module

public import Mathlib

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace GlobalTheory

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]


theorem norm_dotProduct_mulVec_star_le (A : Matrix n n ℂ) (x : n → ℂ) :
    ‖x ⬝ᵥ A *ᵥ star x‖ ≤ ‖A‖ * ∑ k, ‖x k‖ ^ 2 := by
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 (star x) with hy
  have h := l2_opNorm_mulVec A y
  have h1 := norm_inner_le_norm (𝕜 := ℂ) y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y))
  have h2 : ‖y‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by simp [hy, EuclideanSpace.norm_sq_eq]
  have h3 : inner ℂ y ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ y)) = x ⬝ᵥ A *ᵥ star x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [hy]
  rw [← h3, ← h2]
  refine h1.trans ?_
  nlinarith [norm_nonneg y]

end OpNorm

section LogDet

variable {n : Type*} [Fintype n] [DecidableEq n]

end LogDet

section Inertia

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    x ⬝ᵥ diagonal d *ᵥ star x = ∑ k, d k * ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

theorem le_re_dotProduct_diagonal_add_of_support {j : n → ℂ} (E : Matrix n n ℂ) {x : n → ℂ}
    (hx : ∀ k, x k ≠ 0 → j k = 1) :
    (1 - ‖E‖) * ∑ k, ‖x k‖ ^ 2 ≤ (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re := by
  have h1 : (x ⬝ᵥ diagonal j *ᵥ star x).re = ∑ k, ‖x k‖ ^ 2 := by
    rw [dotProduct_diagonal_mulVec_star, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : x k = 0
    · simp [h]
    · rw [hx k h, one_mul, Complex.ofReal_re]
  have h2 := norm_dotProduct_mulVec_star_le E x
  have h3 := abs_le.1 (Complex.abs_re_le_norm (x ⬝ᵥ E *ᵥ star x))
  rw [add_mulVec, dotProduct_add, Complex.add_re, h1]
  linarith [h3.1]

theorem sum_norm_sq_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < ∑ k, ‖x k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ k, by have : x k ≠ 0 := hk; positivity⟩

theorem re_dotProduct_diagonal_add_pos_of_support {j : n → ℂ} {E : Matrix n n ℂ} (hE : ‖E‖ < 1)
    {x : n → ℂ} (hx0 : x ≠ 0) (hx : ∀ k, x k ≠ 0 → j k = 1) :
    0 < (x ⬝ᵥ (diagonal j + E) *ᵥ star x).re :=
  (mul_pos (by linarith) (sum_norm_sq_pos hx0)).trans_le
    (le_re_dotProduct_diagonal_add_of_support E hx)

theorem posDef_one_add {E : Matrix n n ℂ} (hE : E.IsHermitian) (hE1 : ‖E‖ < 1) :
    (1 + E).PosDef := by
  have hH : (1 + E).IsHermitian := isHermitian_one.add hE
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h := re_dotProduct_diagonal_add_pos_of_support (j := fun _ => 1) hE1
    (star_ne_zero.2 hx) fun _ _ => rfl
  rw [star_star, diagonal_one] at h
  rw [Complex.pos_iff]
  exact ⟨h, (hH.im_star_dotProduct_mulVec_self x).symm⟩

end Inertia

section Exp

open NormedSpace

theorem norm_exp_sub_one_sub_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (x : A) : ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h1 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have h2 := (hasSum_nat_add_iff' 2).2 (exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    ← sub_sub] at h1 h2
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun k => ?_
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  gcongr
  exact norm_pow_le' x (by omega)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Exp

end GlobalTheory
