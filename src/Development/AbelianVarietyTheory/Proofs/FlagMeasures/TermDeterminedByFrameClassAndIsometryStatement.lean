module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometry
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_determined_by_frameClass_and_isometry : GlobalTheory.TypeAsm.InjC := by
  first | exact @GlobalTheory.TypeAsm.InjProof.injC | exact GlobalTheory.TypeAsm.InjProof.injC | (intros; apply GlobalTheory.TypeAsm.InjProof.injC <;> assumption)
