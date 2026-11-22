module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTraceLevelCompatible_proof : GlobalTheory.BaseCmp.TraceLevel := by
  first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)
