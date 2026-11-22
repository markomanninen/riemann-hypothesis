module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommuteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorDbarOperatorPullbackConstantFormHolomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDzStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement

@[expose] public section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_chainRule_holomorphicPullback : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m), IsOpen U → v ∈ U → DifferentiableOn ℂ τ U →
    (∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) →
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  first | exact @GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | exact GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | (intros; apply GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp <;> assumption)
