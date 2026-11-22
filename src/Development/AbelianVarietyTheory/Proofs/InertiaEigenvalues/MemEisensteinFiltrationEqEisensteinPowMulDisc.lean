module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

@[expose] public section

noncomputable section

namespace GlobalTheory.FilDiv

open PowerSeries Filter Topology GlobalTheory.BK

section
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

theorem FilPre_le_E_pow (j : ℕ) {g : S O K e} (hg : g ∈ FilPre O K l e j) :
    ∃ q ∈ Rpi (O := O) (K := K) l e, (g : K⟦X⟧) = E K l e ^ j * q := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    refine ⟨C (((m + j).factorial : K)⁻¹) * E K l e ^ m,
      mul_mem (HasK.C_mem _) (pow_mem (E_mem l e _) m), ?_⟩
    rw [hx, Ediv]; ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, h⟩ := hx
    obtain ⟨q', hq', h'⟩ := hy
    exact ⟨q + q', add_mem hq hq', by rw [Subalgebra.coe_add, h, h', mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨q, hq, h⟩ := hx
    exact ⟨c * q, mul_mem (S_le_R l e c.2) hq, by
      rw [smul_eq_mul, Subalgebra.coe_mul, h]; ring⟩

theorem norm_coeff_pow_mul_le (n : ℕ) {h : K⟦X⟧} (hh : h ∈ S O K e) (k : ℕ) :
    ‖coeff k ((l : K⟦X⟧) ^ n * h)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  rw [← map_natCast (C : K →+* K⟦X⟧), ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine le_trans ?_ (hh.1 k)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (k / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le k e)

theorem norm_coeff_E_le (k : ℕ) : ‖coeff k (E K l e)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ := by
  have he := NeZero.ne e
  rw [E, map_add (f := _), coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
  by_cases hk : k = e
  · rw [if_pos hk, if_neg (by omega), add_zero, norm_one, one_mul, hk, rad_pow (K := K) l e]
  · by_cases h0 : k = 0
    · rw [if_neg hk, if_pos h0, zero_add, h0, pow_zero, mul_one]
    · rw [if_neg hk, if_neg h0, add_zero, norm_zero, zero_mul]
      exact norm_nonneg _

variable [CompleteSpace K]

theorem norm_coeff_quotE_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  have hρ := rad_pos l (1 / (e : ℝ))
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  rw [quotE, coeff_mk]
  have h1 : ‖tail l e r (k + e)‖ ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ _), norm_term_eq]
    exact hr _
  calc ‖tail l e r (k + e)‖ * rad l (1 / e) ^ k
      ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) * rad l (1 / e) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(l : K)‖ ^ n := by
        rw [pow_add (rad l (1 / (e : ℝ))) k e, rad_pow (K := K) l e, pow_succ]
        field_simp

theorem norm_coeff_rem_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (r - E K l e * quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hw : ∀ i, 0 ≤ rad l (1 / (e : ℝ)) ^ i := fun i => pow_nonneg (rad_nonneg _ _) i
  rw [sub_eq_add_neg]
  refine (norm_coeff_add_le hw _ _ k).trans (max_le (hr k) ?_)
  rw [map_neg, norm_neg, pow_succ']
  exact norm_coeff_mul_le (w := fun i => rad l (1 / (e : ℝ)) ^ i) hw (fun i j => (pow_add _ i j).le)
    (norm_nonneg _) (by positivity) (norm_coeff_E_le l e) (norm_coeff_quotE_le l e hr) k

theorem exists_eq_E_pow_mul (j : ℕ) {ψ : K⟦X⟧} (hψ : ψ ∈ Rpi (O := O) (K := K) l e)
    (H : ∀ n : ℕ, ∃ q ∈ Rpi (O := O) (K := K) l e,
      ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) :
    ∃ q ∈ Rpi (O := O) (K := K) l e, ψ = E K l e ^ j * q := by
  have quot_mem {f : K⟦X⟧} (hf : f ∈ Rpi (O := O) (K := K) l e) :
      quotE l e f ∈ Rpi (O := O) (K := K) l e := by
    have hρ := rad_pos l (1 / (e : ℝ))
    have htail : Tendsto (fun n => ‖tail l e f n‖ * rad l (1 / e) ^ n) atTop (𝓝 0) := by
      have hcoeff := mem_R.1 hf
      rw [Metric.tendsto_atTop] at hcoeff ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hcoeff (ε / 2) (half_pos hε)
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      refine lt_of_le_of_lt ?_ (half_lt_self hε)
      rw [← le_div_iff₀ (pow_pos hρ n)]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
      rw [le_div_iff₀ (pow_pos hρ n), norm_term_eq]
      have hj := hN (n + j * e) (by omega)
      rw [Real.dist_eq, sub_zero] at hj
      exact (le_abs_self _).trans hj.le
    have hshift := (htail.comp (tendsto_add_atTop_nat e)).mul_const (rad l (1 / e) ^ e)⁻¹
    rw [zero_mul] at hshift
    refine mem_R.2 (hshift.congr fun n => ?_)
    simp only [Function.comp, quotE, coeff_mk]
    rw [pow_add, mul_assoc, mul_inv_cancel_right₀ (pow_pos hρ e).ne']
  have coeff_rem {f : K⟦X⟧} (hf : f ∈ Rpi (O := O) (K := K) l e) (n : ℕ) :
      coeff (n + e) (f - E K l e * quotE l e f) = 0 := by
    have tail_rec (m : ℕ) : tail l e f m = coeff m f - l * tail l e f (m + e) := by
      have hs : Summable fun j : ℕ => coeff (m + j * e) f * (-(l : K)) ^ j := by
        refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
        rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
        have h := ((mem_R.1 hf).comp (tendsto_add_mul e m)).mul_const (rad l (1 / e) ^ m)⁻¹
        rw [zero_mul] at h
        refine h.congr fun j => ?_
        simp only [Function.comp]
        rw [← norm_term_eq (K := K) l e, mul_inv_cancel_right₀ (pow_pos (rad_pos l _) m).ne']
      rw [tail, hs.tsum_eq_zero_add, tail, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
      congr 1
      · simp
      · refine tsum_congr fun j => ?_
        rw [show m + (j + 1) * e = m + e + j * e by ring]
        ring
    rw [map_sub, coeff_E_mul, quotE, coeff_mk, coeff_mk, tail_rec (n + e)]
    ring
  have zero_of_coeff {g : K⟦X⟧} (hg : g ∈ Rpi (O := O) (K := K) l e)
      (h : ∀ n, coeff (n + e) (E K l e * g) = 0) : g = 0 := by
    ext n
    have hcoeff : ∀ j, coeff n g = coeff (n + j * e) g * (-(l : K)) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hj := h (n + j * e)
        rw [coeff_E_mul] at hj
        rw [ih, show n + (j + 1) * e = n + j * e + e by ring]
        linear_combination (-(l : K)) ^ j * hj
    have ht := (mem_R.1 hg).comp (tendsto_add_mul e n)
    have hzero : ‖coeff n g‖ * rad l (1 / e) ^ n = 0 := by
      refine tendsto_nhds_unique tendsto_const_nhds (ht.congr fun j => ?_)
      simp only [Function.comp]
      rw [← norm_term_eq (K := K) l e, ← hcoeff]
    simpa [(rad_pos l _).ne'] using hzero
  induction j generalizing ψ with
  | zero => exact ⟨ψ, hψ, by simp⟩
  | succ j ih =>
    have hQ := quot_mem hψ
    have key : ∀ n, ∃ q ∈ Rpi (O := O) (K := K) l e,
        (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
        ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
      intro n
      obtain ⟨q, hq, hr⟩ := H (n + 1)
      have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi (O := O) (K := K) l e :=
        sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
      generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
      have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
        refine zero_of_coeff (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
          (quot_mem hrR)) fun m => ?_
        have h1 := coeff_rem hψ m
        have h2 := coeff_rem hrR m
        have : E K l e * (quotE l e ψ - E K l e ^ j * q - quotE l e r) =
            (r - E K l e * quotE l e r) - (ψ - E K l e * quotE l e ψ) := by
          rw [← hr_def]; ring
        rw [this, map_sub, h1, h2, sub_zero]
      have hg' : quotE l e ψ - E K l e ^ j * q = quotE l e r := sub_eq_zero.1 hg
      have hrem : ψ - E K l e * quotE l e ψ = r - E K l e * quotE l e r := by
        rw [← hg', ← hr_def]; ring
      exact ⟨q, hq, fun k => by rw [hg']; exact norm_coeff_quotE_le l e hr k,
        fun k => by rw [hrem]; exact norm_coeff_rem_le l e hr k⟩
    choose qs hqs hsmall hrem using key
    obtain ⟨q, hq, hQ'⟩ := ih hQ fun n => ⟨qs n, hqs n, hsmall n⟩
    have hR0 : ψ - E K l e * quotE l e ψ = 0 := by
      ext k
      rw [map_zero]
      have hρ := pow_pos (rad_pos l (1 / (e : ℝ))) k
      have ht : Tendsto (fun n : ℕ => ‖(l : K)‖ ^ (n + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
          (tendsto_add_atTop_nat 1)
      have h0 : ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ 0 :=
        ge_of_tendsto' ht fun n => hrem n k
      exact norm_le_zero_iff.1 (le_of_mul_le_mul_right (by simpa using h0) hρ)
    refine ⟨q, hq, ?_⟩
    rw [sub_eq_zero] at hR0
    rw [hR0, hQ', pow_succ']; ring

end

theorem mem_Fil_eq_E_pow_mul : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j →
      ∃ q ∈ Rpi (O := O) (K := K) l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have hψ : (φ : K⟦X⟧) ∈ Rpi (O := O) (K := K) l e := S_le_R l e φ.2
  refine exists_eq_E_pow_mul l e j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := FilPre_le_E_pow l e j hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k

end GlobalTheory.FilDiv
