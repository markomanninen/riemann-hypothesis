module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS

@[expose] public section

open BpJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional : ThmBpDS := by
  first | exact @GlobalTheory.discreteSeriesCoef_pointwiseBound | exact GlobalTheory.discreteSeriesCoef_pointwiseBound | (intros; apply GlobalTheory.discreteSeriesCoef_pointwiseBound <;> assumption)
