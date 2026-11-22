module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect

@[expose] public section

open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)
