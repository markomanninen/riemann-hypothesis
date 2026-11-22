module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → AddMonoidAlgebra.coeff P α = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  first | exact @GlobalTheory.trunc_dec | exact GlobalTheory.trunc_dec | (intros; apply GlobalTheory.trunc_dec <;> assumption)
