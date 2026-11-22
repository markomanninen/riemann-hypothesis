module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDisc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

@[expose] public section

open PowerSeries Filter Topology GlobalTheory.BK GlobalTheory.FilDiv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j → ∃ q ∈ Rpi (O := O) (K := K) l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have filPre_divisible : ∀ {g : S O K e}, g ∈ FilPre O K l e j →
      ∃ q ∈ Rpi (O := O) (K := K) l e, (g : K⟦X⟧) = E K l e ^ j * q := by
    intro g hg
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
  have divisible_of_approximation : ∀ (j : ℕ) {ψ : K⟦X⟧}, ψ ∈ Rpi (O := O) (K := K) l e →
      (∀ n : ℕ, ∃ q ∈ Rpi (O := O) (K := K) l e,
        ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) →
      ∃ q ∈ Rpi (O := O) (K := K) l e, ψ = E K l e ^ j * q := by
    intro j ψ hψ H
    induction j generalizing ψ with
    | zero => exact ⟨ψ, hψ, by simp⟩
    | succ j ih =>
      have hQ := quotE_mem_Rpi l e hψ
      have key : ∀ n, ∃ q ∈ Rpi (O := O) (K := K) l e,
          (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
          ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
        intro n
        obtain ⟨q, hq, hr⟩ := H (n + 1)
        have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi (O := O) (K := K) l e :=
          sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
        generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
        have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
          refine eq_zero_of_E_mul l e (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
            (quotE_mem_Rpi l e hrR)) fun m => ?_
          have h1 := coeff_sub_E_mul_quotE l e hψ m
          have h2 := coeff_sub_E_mul_quotE l e hrR m
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
  have hψ : (φ : K⟦X⟧) ∈ Rpi (O := O) (K := K) l e := S_le_R l e φ.2
  refine divisible_of_approximation j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := filPre_divisible hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k
