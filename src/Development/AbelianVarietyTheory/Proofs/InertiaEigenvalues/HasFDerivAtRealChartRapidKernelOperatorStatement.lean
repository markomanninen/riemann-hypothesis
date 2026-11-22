module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ∃ L : Lie E a →L[ℝ] ℂ, HasFDerivAt (chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g) L (toL y.val) ∧ ∀ Z : Lie E a, L Z = ∫ x, k x * lieD (toL (((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val)) G (g * infGL E a (y * γ x)) ∂ν := by
  first | exact @GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | exact GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | (intros; apply GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel <;> assumption)
