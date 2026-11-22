module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer

@[expose] public section

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem unramifiedOrthogonality : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  UnrOrth.unramifiedOrthogonality_of localFiniteness localTateDuality
    LocalEuler.localEulerChar_holds

end GlobalTheory.CompanionTheory.Hypotheses₂
