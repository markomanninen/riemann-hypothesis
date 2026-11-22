module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationDecompositionFiniteDifferences
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeValuesNegativeIntegerRationalStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeTilingBySignRegionsStatement

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_values_negative_integers_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational <;> assumption)
