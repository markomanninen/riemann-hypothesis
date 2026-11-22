module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPAddSubWeierstrassPSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul : ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z - w ∉ L.lattice → z + w ∉ L.lattice → (L.weierstrassP z - L.weierstrassP w) ^ 2 * (L.weierstrassP (z + w) - L.weierstrassP (z - w)) = -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  first | exact @GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | exact GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | (intros; apply GlobalTheory.weierstrassP_add_sub_weierstrassP_sub <;> assumption)
