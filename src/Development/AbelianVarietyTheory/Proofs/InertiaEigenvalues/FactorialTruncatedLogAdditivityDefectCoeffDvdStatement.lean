module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect

@[expose] public section

open GlobalTheory.LogU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ, ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  first | exact @GlobalTheory.LogUIntg.logDefect_coeff_dvd | exact GlobalTheory.LogUIntg.logDefect_coeff_dvd | (intros; apply GlobalTheory.LogUIntg.logDefect_coeff_dvd <;> assumption)
