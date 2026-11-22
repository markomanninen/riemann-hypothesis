module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
