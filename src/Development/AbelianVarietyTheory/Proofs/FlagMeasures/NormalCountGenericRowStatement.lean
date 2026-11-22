module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire

@[expose] public section

open Formalism.L2.SG.Pf.MainEqSteps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalCount_genericRow : StepNormalsG := by
  first | exact @GlobalTheory.stepNormalsG_holds | exact GlobalTheory.stepNormalsG_holds | (intros; apply GlobalTheory.stepNormalsG_holds <;> assumption)
