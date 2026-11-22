module

public import Mathlib

@[expose] public section

theorem UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow :
    ∀ (Q T a b : ℕ), Q ≠ 0 → ∏ p ∈ Q.primeFactors.filter Nat.Prime,
      p ^ (T * ⌈(padicValNat p Q : ℝ) * (a : ℝ)⌉.toNat + ⌈(padicValNat p Q : ℝ) * (b : ℝ)⌉.toNat) = Q ^ (T * a + b) := by
  intro Q T a b hQ
  have hc : ∀ m n : ℕ, ⌈(m : ℝ) * (n : ℝ)⌉.toNat = m * n := by
    intro m n
    rw [← Nat.cast_mul, Int.ceil_natCast, Int.toNat_natCast]
  have hf : Q.primeFactors.filter Nat.Prime = Q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  have hQ' : ∏ p ∈ Q.primeFactors, p ^ (Q.factorization p) = Q := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hQ
  rw [hf]
  conv_rhs => rw [← hQ', ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hc, hc, ← pow_mul, Nat.factorization_def Q (Nat.prime_of_mem_primeFactors hp),
    Nat.padicValNat_def]
  congr 1
  ring
