module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_uniqueness_characterisation : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachCharacterisation D HW F := by
  first | exact @GlobalTheory.NL.FrobeniusMatrixUniqueness.main | exact GlobalTheory.NL.FrobeniusMatrixUniqueness.main | (intros; apply GlobalTheory.NL.FrobeniusMatrixUniqueness.main <;> assumption)
