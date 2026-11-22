module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | exact GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | (intros; apply GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq <;> assumption)
