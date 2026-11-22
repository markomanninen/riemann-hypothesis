module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLieStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendstoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatchStatement

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_lie_and_group (hM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) :
    UnitLemmaLie ∧ UnitLemmaGroup :=
  have hL : UnitLemmaLie := GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent (GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch hM) GlobalTheory.T.unitary_lattice_count_ratio_tendsto GlobalTheory.T.linearLatticeCountDescent_proof
  ⟨hL, GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie hL⟩

end GlobalTheory.UnitLemma
