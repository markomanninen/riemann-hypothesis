module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWords
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) := by
  first | exact @GlobalTheory.EX.szRow_sizeG_sizeWords | exact GlobalTheory.EX.szRow_sizeG_sizeWords | (intros; apply GlobalTheory.EX.szRow_sizeG_sizeWords <;> assumption)
