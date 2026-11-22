module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionCutoffMulHolomorphic
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothSection_cutoff_mul_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  first | exact @GlobalTheory.smooth_cutoff_mul_sec | exact GlobalTheory.smooth_cutoff_mul_sec | (intros; apply GlobalTheory.smooth_cutoff_mul_sec <;> assumption)
