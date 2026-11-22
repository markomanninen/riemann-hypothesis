module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff

@[expose] public section

open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowFun.coeff_funOf_mem_range | exact GlobalTheory.RowFun.coeff_funOf_mem_range | (intros; apply GlobalTheory.RowFun.coeff_funOf_mem_range <;> assumption)
