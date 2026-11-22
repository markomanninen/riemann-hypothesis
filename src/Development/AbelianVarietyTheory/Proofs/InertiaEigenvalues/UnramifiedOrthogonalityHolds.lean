module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnramifiedOrthogonality

@[expose] public section

namespace GlobalTheory

theorem unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality

end GlobalTheory
