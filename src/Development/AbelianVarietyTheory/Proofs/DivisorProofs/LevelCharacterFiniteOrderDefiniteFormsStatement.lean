module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterFiniteOrderDefiniteForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_finiteOrder_definite_forms : GlobalTheory.BaseCmp.LevLamRoot := by
  first | exact @GlobalTheory.BaseCmp.levLamRoot | exact GlobalTheory.BaseCmp.levLamRoot | (intros; apply GlobalTheory.BaseCmp.levLamRoot <;> assumption)
