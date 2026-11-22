module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_weight_bounded : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l → (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic <;> assumption)
