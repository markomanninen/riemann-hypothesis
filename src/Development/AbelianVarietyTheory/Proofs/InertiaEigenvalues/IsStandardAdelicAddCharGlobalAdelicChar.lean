module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep

namespace GlobalTheory.StdCharStd

theorem stdPsi_adelicChar : ∀ (E : Type) [Field E] [NumberField E],
    GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) :=
  fun E _ _ => GlobalTheory.StdCharConductor.stdPsi_psi E

end GlobalTheory.StdCharStd
