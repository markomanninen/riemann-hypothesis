module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPde
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde : SzRow (fun _ _ L => SizeCond L ∧ SizeQD L ∧ SizePde L) := by
  first | exact @GlobalTheory.EX.szRow_cond_qd_pde | exact GlobalTheory.EX.szRow_cond_qd_pde | (intros; apply GlobalTheory.EX.szRow_cond_qd_pde <;> assumption)
