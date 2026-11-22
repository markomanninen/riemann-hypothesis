module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

@[expose] public section

open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_identity_of_local_densities : Scal → LocR → ThetaId := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)
