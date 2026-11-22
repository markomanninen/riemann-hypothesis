module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakSolutionOfSmoothSolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
public import Formalism.UnipotentAdelicQuotients.EllRegCheck

@[expose] public section

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakSolution_of_smooth_solution : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  first | exact @GlobalTheory.HCA.weakSol_of_smooth | exact GlobalTheory.HCA.weakSol_of_smooth | (intros; apply GlobalTheory.HCA.weakSol_of_smooth <;> assumption)
