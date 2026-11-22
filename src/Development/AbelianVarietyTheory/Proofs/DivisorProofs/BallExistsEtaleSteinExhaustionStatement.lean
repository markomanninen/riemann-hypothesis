module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustion
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_exists_etaleStein_exhaustion : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  first | exact @GlobalTheory.BallStein.ball_etaleStein | exact GlobalTheory.BallStein.ball_etaleStein | (intros; apply GlobalTheory.BallStein.ball_etaleStein <;> assumption)
