module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2

@[expose] public section

namespace GlobalTheory.Laid

theorem loceuler_holds : ReciprocityTheory.Gal.LocalEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

end GlobalTheory.Laid
