module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultVTwistedDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotDRLOfTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateTwistMultiplicationIntertwines
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
