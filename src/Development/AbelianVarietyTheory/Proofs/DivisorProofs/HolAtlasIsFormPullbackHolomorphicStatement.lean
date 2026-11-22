module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement

@[expose] public section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_isForm_pullback_holomorphic : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) := by
  first | exact @GlobalTheory.PullbackForm.isForm_pullback | exact GlobalTheory.PullbackForm.isForm_pullback | (intros; apply GlobalTheory.PullbackForm.isForm_pullback <;> assumption)
