module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CovolumeUnitDetNormSlabLatticeAutLtTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_unitDetNormSlab_latticeAut_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  letI : Submodule.IsFullLattice E Λ := hΛ
  apply GlobalTheory.SlabFinVol.covol_unitSlab_lt_top <;> first | assumption | infer_instance
