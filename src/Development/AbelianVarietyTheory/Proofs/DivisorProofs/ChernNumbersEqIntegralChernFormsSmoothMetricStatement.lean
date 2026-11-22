module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
