module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs : ∀ (p q : ℕ), cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  first | exact @GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | exact GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | (intros; apply GlobalTheory.CayleyBlock.cayOp_pow_eq_sum <;> assumption)
