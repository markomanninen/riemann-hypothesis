module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_flat_separately_harmonic : ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O → (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | exact GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero <;> assumption)
