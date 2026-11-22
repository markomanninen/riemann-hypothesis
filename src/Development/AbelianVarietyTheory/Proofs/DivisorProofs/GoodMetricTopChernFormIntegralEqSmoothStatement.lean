module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  first | exact @GlobalTheory.GoodTop.goodTopChernForm | exact GlobalTheory.GoodTop.goodTopChernForm | (intros; apply GlobalTheory.GoodTop.goodTopChernForm <;> assumption)
