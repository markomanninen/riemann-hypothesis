module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  first | exact @GlobalTheory.sq_sum_equiv_Ico | exact GlobalTheory.sq_sum_equiv_Ico | (intros; apply GlobalTheory.sq_sum_equiv_Ico <;> assumption)
