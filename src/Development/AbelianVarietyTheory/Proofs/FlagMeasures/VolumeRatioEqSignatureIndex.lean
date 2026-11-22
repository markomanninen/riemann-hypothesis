module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩


end GlobalTheory.RowIndex
