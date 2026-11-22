module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRel
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)
