module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localHaarMeasures_pullback_realGroup : GlobalTheory.TypeAsm.PullC := by
  first | exact @GlobalTheory.PullbackComparison.pullC_holds | exact GlobalTheory.PullbackComparison.pullC_holds | (intros; apply GlobalTheory.PullbackComparison.pullC_holds <;> assumption)
