module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportional
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation

@[expose] public section

open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorialWeightedPairing_detPow_proportional : (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (Y - M) * Q) A) * (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A) = (∑ A ∈ (cayDet n₀ C ^ M).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ M) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) * (∑ A ∈ (cayDet n₀ C ^ Y).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ Y) A)) := by
  first | exact @GlobalTheory.DetPowPairing.pairing_pow_proportional | exact GlobalTheory.DetPowPairing.pairing_pow_proportional | (intros; apply GlobalTheory.DetPowPairing.pairing_pow_proportional <;> assumption)
