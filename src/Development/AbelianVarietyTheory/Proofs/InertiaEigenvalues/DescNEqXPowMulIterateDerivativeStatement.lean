module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧),
      descN (K := K) p f = X ^ p * (⇑(derivative (R := K)))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative, ← Nat.add_descFactorial_eq_ascFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge h), Nat.cast_zero, zero_mul]
