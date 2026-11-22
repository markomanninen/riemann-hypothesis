module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

@[expose] public section

open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_value_highest_weight_vector : GlobalTheory.LeviCut.StepScalar := by
  first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)
