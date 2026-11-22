module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_local_identity : EllLocal := by
  first | exact @GlobalTheory.CompanionTheory.EllLoc.ellLocal | exact GlobalTheory.CompanionTheory.EllLoc.ellLocal | (intros; apply GlobalTheory.CompanionTheory.EllLoc.ellLocal <;> assumption)
