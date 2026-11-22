module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExists
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists : GlobalTheory.TypeAsm.FundC := by
  first | exact @GlobalTheory.TypeAsm.fundC_holds | exact GlobalTheory.TypeAsm.fundC_holds | (intros; apply GlobalTheory.TypeAsm.fundC_holds <;> assumption)
