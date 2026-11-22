module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPMulProdTranslateKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → ∀ z, α * z ∉ L.lattice → L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t) = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  first | exact @GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel | exact GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel | (intros; apply GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel <;> assumption)
