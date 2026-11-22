module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_twist_identity : ThTwist := by
  first | exact @GlobalTheory.CompanionTheory.ThTw.thTwist | exact GlobalTheory.CompanionTheory.ThTw.thTwist | (intros; apply GlobalTheory.CompanionTheory.ThTw.thTwist <;> assumption)
