module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgebraicNumberCongrModPrimePow
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

@[expose] public section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumber_congr_mod_prime_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
      IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) →
      ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e →
      ∃ a ∈ A, Cong (p := p) k e (j a) := by
  intro Ω _ _ _ p hp A Ωl _ _ hclo j hA k e he halg
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcong : ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
    obtain ⟨P, hP0, hP⟩ := halg
    have : CharZero Ωl := Basic.charZero_of_isClo hclo
    have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨v, hv, _, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ωl hclo
    set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
    have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
    have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
    have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
    have hc : φ P.leadingCoeff ≠ 0 := by
      rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
      exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
    have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
    obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
      (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
    have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
    have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
      hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
    obtain ⟨Q, R, hdeg, hQR⟩ := Dense.exists_approx P N
    have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
      intro y hy
      rw [map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le hy
    have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
      have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
      simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
      rw [map_pow, map_natCast] at this
      exact this
    have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
      rw [eq_sub_of_add_eq hco.symm]
      exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
    have hQ0 : Q.coeff P.natDegree ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, map_zero] at hvQ
      exact hvc.ne hvQ
    have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
    have hRe : v (R.eval₂ φ e) ≤ 1 := by
      rw [eval₂_eq_sum_range]
      refine Valuation.map_sum_le v fun i _ => ?_
      rw [map_mul, map_pow]
      exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
    have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
      rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
        RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
      exact eq_neg_of_add_eq_zero_left hPe
    obtain ⟨a, ha⟩ := Dense.exists_near_root v j e (v (p : Ωl) ^ k) Q (by
      rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
      exact (hsmall _ hRe).trans_lt hN)
    refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
    · rw [show j a = e - (e - j a) by ring]
      exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
    · rw [map_div₀, map_pow]
      exact div_le_one_of_le₀ ha.le zero_le
    · field_simp
  obtain ⟨a, ha, hc⟩ := hcong
  exact ⟨a, (hA a).2 ha, hc⟩
