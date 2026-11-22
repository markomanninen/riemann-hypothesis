module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohFin
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohField
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal

@[expose] public section

namespace GlobalTheory.Laid

theorem locfin_holds : ReciprocityTheory.Gal.LocalFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

end GlobalTheory.Laid
