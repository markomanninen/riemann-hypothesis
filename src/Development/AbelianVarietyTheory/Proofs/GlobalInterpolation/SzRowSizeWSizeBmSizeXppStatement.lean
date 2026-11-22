module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXpp
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  first | exact @GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp | exact GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp | (intros; apply GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp <;> assumption)
