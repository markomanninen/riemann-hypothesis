module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonicStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChartStatement

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
