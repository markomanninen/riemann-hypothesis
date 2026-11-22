module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemHalfLatticeOfOddMultiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier : ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  first | exact @GlobalTheory.CMModel.mem_lattice_of_even_kerReps | exact GlobalTheory.CMModel.mem_lattice_of_even_kerReps | (intros; apply GlobalTheory.CMModel.mem_lattice_of_even_kerReps <;> assumption)
