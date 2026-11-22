module

public import Mathlib
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

namespace GlobalTheory

theorem coeff_mem_of_poly_values_mem : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (N : ℕ) (c : ℕ → V), (∀ u : ℂ, ∑ k ∈ Finset.range N, u ^ k • c k ∈ S) → ∀ k < N, c k ∈ S := by
  intro V _ _ S N c h k hk
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range N,
    Polynomial.C (f (Submodule.Quotient.mk (c j))) * Polynomial.X ^ j with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have h1 : S.mkQ (∑ k ∈ Finset.range N, u ^ k • c k) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h u)
    have h0 := congrArg f h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, smul_eq_mul, map_zero] at h0
    simp only [hpdef, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hp
  simp only [hpdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range.mpr hk] using hc

end GlobalTheory
