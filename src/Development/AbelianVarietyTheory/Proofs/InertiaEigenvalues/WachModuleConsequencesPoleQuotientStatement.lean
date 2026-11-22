module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaSemisimpleQuotientD_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | exact GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient <;> assumption)
