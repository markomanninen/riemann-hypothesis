module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
