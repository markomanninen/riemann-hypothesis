module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudes
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes : GlobalTheory.TypeAsm.FactC := by
  first | exact @GlobalTheory.TypeAsm.factC_holds | exact GlobalTheory.TypeAsm.factC_holds | (intros; apply GlobalTheory.TypeAsm.factC_holds <;> assumption)
