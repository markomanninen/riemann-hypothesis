module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_model_change : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ModelChange := by
  first | exact @GlobalTheory.ModelChg.modelChange | exact GlobalTheory.ModelChg.modelChange | (intros; apply GlobalTheory.ModelChg.modelChange <;> assumption)
