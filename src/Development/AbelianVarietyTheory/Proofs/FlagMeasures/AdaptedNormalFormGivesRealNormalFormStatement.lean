module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedNormalForm_gives_real_normal_form : GlobalTheory.TypeAsm.FrameC := by
  first | exact @GlobalTheory.TypeAsm.frameC_holds | exact GlobalTheory.TypeAsm.frameC_holds | (intros; apply GlobalTheory.TypeAsm.frameC_holds <;> assumption)
