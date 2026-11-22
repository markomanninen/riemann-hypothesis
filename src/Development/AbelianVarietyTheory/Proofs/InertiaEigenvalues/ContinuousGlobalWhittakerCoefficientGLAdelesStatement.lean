module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  first | (exact @GlobalTheory.JSW.WhitCont.continuous_whit) | (exact GlobalTheory.JSW.WhitCont.continuous_whit) | (intros; apply GlobalTheory.JSW.WhitCont.continuous_whit  <;> assumption)
