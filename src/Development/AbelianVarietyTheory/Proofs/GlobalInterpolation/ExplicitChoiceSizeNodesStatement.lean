module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  first | exact @GlobalTheory.EX.szRow_sizeNodes | exact GlobalTheory.EX.szRow_sizeNodes | (intros; apply GlobalTheory.EX.szRow_sizeNodes <;> assumption)
