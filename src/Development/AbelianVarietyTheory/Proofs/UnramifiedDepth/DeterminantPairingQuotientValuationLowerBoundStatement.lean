module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBound
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

@[expose] public section

open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  first | exact @GlobalTheory.DetPairingBound.main | exact GlobalTheory.DetPairingBound.main | (intros; apply GlobalTheory.DetPairingBound.main <;> assumption)
