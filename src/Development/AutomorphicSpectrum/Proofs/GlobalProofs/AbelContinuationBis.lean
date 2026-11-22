module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abel_continuation : AbelContinuation := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation <;> assumption)
