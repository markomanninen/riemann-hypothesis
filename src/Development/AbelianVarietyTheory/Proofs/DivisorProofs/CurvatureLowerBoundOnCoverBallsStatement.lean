module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBalls
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_lower_bound_on_cover_balls : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  first | exact @GlobalTheory.OTY.CoverCurv.curv_cover | exact GlobalTheory.OTY.CoverCurv.curv_cover | (intros; apply GlobalTheory.OTY.CoverCurv.curv_cover <;> assumption)
