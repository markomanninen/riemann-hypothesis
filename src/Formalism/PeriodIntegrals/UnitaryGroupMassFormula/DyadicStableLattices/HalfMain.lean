module

public import Formalism.PeriodIntegrals.GoodTwo
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt

@[expose] public section

noncomputable section

namespace PI.GoodTwo.HalfW

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

theorem twist : Twist := by
  intro K _ _ _ W g2 g3 hΔ hg hrel
  have hc := W.c_relation
  have key : 27 * W.c₄ ^ 3 * g3 ^ 2 = g2 ^ 3 * W.c₆ ^ 2 := by
    linear_combination (-1 : K) * hrel - g2 ^ 3 * hc
  have hD : W.c₄ ^ 3 - W.c₆ ^ 2 ≠ 0 := by
    rw [← hc]; exact mul_ne_zero (by norm_num) hΔ
  by_cases h2 : g2 = 0
  · have h3 : g3 ≠ 0 := by
      rintro rfl; apply hg; rw [h2]; ring
    have hc4 : W.c₄ = 0 := by
      have h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0 := by rw [key, h2]; ring
      simpa [h3] using h0
    have hc6 : W.c₆ ≠ 0 := by
      intro h; apply hD; rw [hc4, h]; ring
    have hw : W.c₆ / 216 / g3 ≠ 0 := div_ne_zero (div_ne_zero hc6 (by norm_num)) h3
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 / g3) (by norm_num : 0 < 6)
    refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
    · rw [hc4, h2]; ring
    · rw [hu]; field_simp
  by_cases h3 : g3 = 0
  · have hc6 : W.c₆ = 0 := by
      have h0 : g2 ^ 3 * W.c₆ ^ 2 = 0 := by rw [← key, h3]; ring
      simpa [h2] using h0
    have hc4 : W.c₄ ≠ 0 := by
      intro h; apply hD; rw [hc6, h]; ring
    have hw : W.c₄ / 12 / g2 ≠ 0 := div_ne_zero (div_ne_zero hc4 (by norm_num)) h2
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₄ / 12 / g2) (by norm_num : 0 < 4)
    refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
    · rw [hu]; field_simp
    · rw [hc6, h3]; ring
  have hc4 : W.c₄ ≠ 0 := by
    intro h
    have h0 : g2 ^ 3 * W.c₆ ^ 2 = 0 := by rw [← key, h]; ring
    have hc6 : W.c₆ = 0 := by simpa [h2] using h0
    apply hD; rw [hc6, h]; ring
  have hc6 : W.c₆ ≠ 0 := by
    intro h
    have h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0 := by rw [key, h]; ring
    apply hc4; simpa [h3] using h0
  have hA : W.c₄ / 12 ≠ 0 := div_ne_zero hc4 (by norm_num)
  have hB : W.c₆ / 216 ≠ 0 := div_ne_zero hc6 (by norm_num)
  have keyAB : (W.c₄ / 12) ^ 3 * g3 ^ 2 = g2 ^ 3 * (W.c₆ / 216) ^ 2 := by
    linear_combination (1 / 46656 : K) * key
  have hw : W.c₆ / 216 * g2 / (W.c₄ / 12 * g3) ≠ 0 :=
    div_ne_zero (mul_ne_zero hB h2) (mul_ne_zero hA h3)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) (by norm_num : 0 < 2)
  have hw2 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 2 * g2 = W.c₄ / 12 := by
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 (mul_ne_zero hA h3))]
    linear_combination (-1 : K) * keyAB
  have hw3 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 3 * g3 = W.c₆ / 216 := by
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 3 (mul_ne_zero hA h3))]
    linear_combination (-(W.c₆ / 216 * g3)) * keyAB
  refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
  · rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu, hw2]
  · rw [show u ^ 6 = (u ^ 2) ^ 3 by ring, hu, hw3]

end PI.GoodTwo.HalfW
