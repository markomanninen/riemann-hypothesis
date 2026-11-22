module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m (d⁄dX^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  rw [PowerSeries.coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]

theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * d⁄dX^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
