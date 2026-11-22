module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import GroundTheory.GlobalFields.TateThesis.AdelicChar

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  first | exact @GlobalTheory.StdCharStd.stdPsi_adelicChar | exact GlobalTheory.StdCharStd.stdPsi_adelicChar | (intros; apply GlobalTheory.StdCharStd.stdPsi_adelicChar <;> assumption)
