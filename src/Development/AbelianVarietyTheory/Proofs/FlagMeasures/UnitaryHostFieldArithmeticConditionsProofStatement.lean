module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHostFieldArithmeticConditions : GlobalTheory.TypeAsm.HostC := by
  first | exact @GlobalTheory.TypeAsm.hostC | exact GlobalTheory.TypeAsm.hostC | (intros; apply GlobalTheory.TypeAsm.hostC <;> assumption)
