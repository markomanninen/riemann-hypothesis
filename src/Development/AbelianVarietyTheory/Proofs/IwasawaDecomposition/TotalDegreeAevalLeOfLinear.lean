module

public import Mathlib

@[expose] public section

namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
