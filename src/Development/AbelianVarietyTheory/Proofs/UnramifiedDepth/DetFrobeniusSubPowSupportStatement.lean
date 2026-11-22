module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DetFrobeniusSubPowSupport
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

@[expose] public section

open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_frobenius_sub_pow_support_bounds : (∀ (l i E n₀ s : ℕ), l.Prime → 1 ≤ i → ∀ ψ : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ,
    ψ = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) ^ (l ^ i) →
    ∀ m ∈ (ψ ^ s).support, (∑ q, m (Sum.inr q)) ≤ n₀ * s ∧ (∑ q, m (Sum.inl q)) + l ^ i * ∑ q, m (Sum.inr q) = n₀ * l ^ i * s ∧
      (l : ℤ) ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ AddMonoidAlgebra.coeff (ψ ^ s) m) := by
  first | exact @GlobalTheory.det_frobenius_sub_pow_support | exact GlobalTheory.det_frobenius_sub_pow_support | (intros; apply GlobalTheory.det_frobenius_sub_pow_support <;> assumption)
