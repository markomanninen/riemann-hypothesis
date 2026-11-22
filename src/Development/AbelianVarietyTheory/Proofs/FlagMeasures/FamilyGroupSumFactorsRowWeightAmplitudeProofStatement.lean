module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  first | exact @GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | exact GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude | (intros; apply GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude <;> assumption)
