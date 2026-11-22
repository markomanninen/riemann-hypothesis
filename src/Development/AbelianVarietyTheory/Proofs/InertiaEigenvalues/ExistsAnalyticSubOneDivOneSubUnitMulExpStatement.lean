module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_sub_one_div_one_sub_mul_exp : ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  first | exact @GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | exact GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp | (intros; apply GlobalTheory.exists_analytic_sub_one_div_one_sub_unit_mul_exp <;> assumption)
