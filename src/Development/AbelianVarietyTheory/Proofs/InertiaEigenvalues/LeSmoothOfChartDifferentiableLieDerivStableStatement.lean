module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable
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

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)), (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) → (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  first | exact @GlobalTheory.SmoothClosure.le_Sm | exact GlobalTheory.SmoothClosure.le_Sm | (intros; apply GlobalTheory.SmoothClosure.le_Sm <;> assumption)
