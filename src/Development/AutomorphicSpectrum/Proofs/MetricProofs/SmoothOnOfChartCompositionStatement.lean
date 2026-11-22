module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartComposition
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
