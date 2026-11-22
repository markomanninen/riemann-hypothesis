module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpen
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_add_psh_potential_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) (f : X → ℝ) (Θ : LocPot X), IsOpen U → IsPotential A P → IsPotential A Θ → A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) → IsPsh A Θ → IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | exact GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | (intros; apply GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh <;> assumption)
