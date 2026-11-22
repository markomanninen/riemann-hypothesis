module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

@[expose] public section

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ f g : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ f z * g z) = GlobalTheory.PeriodFamily.taylor N t f * GlobalTheory.PeriodFamily.taylor N t g := by
  first | exact @GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | exact GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero <;> assumption)
