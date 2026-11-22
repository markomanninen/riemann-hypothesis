module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  first | exact @GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | exact GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | (intros; apply GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof <;> assumption)
