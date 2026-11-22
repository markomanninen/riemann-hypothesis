module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaQuotientAtPrincipalLevel_proof : GlobalTheory.BaseCmp.FlatTwoStep := by
  first | exact @GlobalTheory.BaseCmp.flatTwoStep_holds | exact GlobalTheory.BaseCmp.flatTwoStep_holds | (intros; apply GlobalTheory.BaseCmp.flatTwoStep_holds <;> assumption)
