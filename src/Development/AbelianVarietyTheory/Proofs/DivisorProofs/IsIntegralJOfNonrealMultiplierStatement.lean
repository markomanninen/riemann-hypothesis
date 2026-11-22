module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_j_of_nonreal_multiplier : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 → _root_.IsIntegral ℤ (latticeCurve L).j := by
  first | exact @GlobalTheory.CMModel.LatticeJInt.main | exact GlobalTheory.CMModel.LatticeJInt.main | (intros; apply GlobalTheory.CMModel.LatticeJInt.main <;> assumption)
