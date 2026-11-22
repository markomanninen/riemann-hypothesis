module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation

@[expose] public section

theorem GlobalTheory.Top.heckeTateFE : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation
