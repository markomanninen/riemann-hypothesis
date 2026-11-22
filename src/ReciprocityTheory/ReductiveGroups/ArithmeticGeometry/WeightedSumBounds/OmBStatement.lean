module

public import Mathlib
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Sh

open ReciprocityTheory.PGsh

noncomputable section

private theorem key {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (lg P : PowerSeries C) (Ω b : C) (M : ℕ) (hM : 2 ≤ M) (β φ r : ℝ) (hβ : 0 < β)
    (hb : v b = β) (hfac : v (M.factorial : C) = φ) (hr : v Ω = r) (hrβ : r < β)
    (hl0 : PowerSeries.coeff 0 lg = 0) (hl1 : PowerSeries.coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j lg = 0)
    (hsub : PowerSeries.subst P lg = b • lg) (hP0 : PowerSeries.coeff 0 P = 0)
    (hP1 : PowerSeries.coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → PowerSeries.coeff j P = 0)
    (hu : v (PowerSeries.coeff M P) = 0) (hint : PsIsInt v (expComp Ω lg)) :
    r - β = M * r - φ := by
  have hc := PowerSeriesCoeffGaps.coeff_subst_gap lg P M hM b hl0 hl1 hlg hP0 hP1 hPg
  rw [hsub, PowerSeries.coeff_smul, smul_eq_mul] at hc
  have hu' : PowerSeries.coeff M P = PowerSeries.coeff M lg * (b + -b ^ M) := by
    linear_combination -hc
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hvb : v (-b ^ M) = ((M * β : ℝ) : WithTop ℝ) := by
    rw [v.map_neg, v.map_pow, hb, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hd : v (b + -b ^ M) = β := PowerSeriesCoeffGaps.add_eq_of_lt v hb hvb (by nlinarith)
  have hk0 : PowerSeries.coeff M lg ≠ 0 := by
    intro h0
    rw [hu', h0, zero_mul, v.map_zero] at hu
    exact WithTop.top_ne_zero hu
  obtain ⟨s, hs⟩ := PowerSeriesCoeffGaps.exists_real v hk0
  have hs' : s = -β := by
    rw [hu', v.map_mul, hs, hd, ← WithTop.coe_add] at hu
    have := WithTop.coe_eq_zero.mp hu
    linarith
  have hI := hint M
  unfold IsIntV at hI
  rw [PowerSeriesCoeffGaps.coeff_expComp_gap Ω lg M hM hl0 hl1 hlg] at hI
  have hx : v (Ω * PowerSeries.coeff M lg) = ((r + -β : ℝ) : WithTop ℝ) := by
    rw [v.map_mul, hr, hs, hs', WithTop.coe_add]
  have hy : v (Ω ^ M / (M.factorial : C)) = ((M * r - φ : ℝ) : WithTop ℝ) :=
    PowerSeriesCoeffGaps.div_eq_coe v (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M))
      (by rw [v.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]) hfac
  have := PowerSeriesCoeffGaps.eq_of_nonneg_add v (by linarith) hx hy hI
  linarith

end

end ReciprocityTheory.ChartRestriction.G.Sh
