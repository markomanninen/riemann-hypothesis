module

public import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_wint_eq_withDensity {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ps : M → ℝ) (hps : Measurable ps) (F : M → ℂ) :
    wint n z F ps = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(vol n z).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ps x))) := by
  unfold wint
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-ps x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hps.neg)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp]
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem fx_lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = eLpNorm' F 2 μ ^ (2 : ℝ) := by
  rw [MeasureTheory.eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_mul]
  norm_num

end

end ReciprocityTheory.L2DbarEstimates.I
