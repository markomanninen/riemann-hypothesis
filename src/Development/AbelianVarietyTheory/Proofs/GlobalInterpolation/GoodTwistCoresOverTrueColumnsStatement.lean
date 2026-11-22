module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumns
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwistCores_over_trueColumns : ∀ (𝒮 : Slots) (R : V4.Slot), OverCols (IsGoodE 𝒮) ∧ OverCols (sAnd (IsGoodE 𝒮) R) := by
  first | exact @GlobalTheory.Fc.Cv.overCols_goodE | exact GlobalTheory.Fc.Cv.overCols_goodE | (intros; apply GlobalTheory.Fc.Cv.overCols_goodE <;> assumption)
