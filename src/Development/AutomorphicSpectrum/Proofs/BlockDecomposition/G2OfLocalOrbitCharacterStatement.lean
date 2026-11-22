module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G2OfLocalOrbitCharacter
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantFactorsProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalComplexCoefficients_of_local_orbit_character : EllLocal → KapOrbAE → ChWMap → GlobalComplexCoefficients := by
  first | exact @GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | exact GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | (intros; apply GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c <;> assumption)
