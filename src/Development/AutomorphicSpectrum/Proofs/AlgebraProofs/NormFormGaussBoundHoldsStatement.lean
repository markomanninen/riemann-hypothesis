module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_form_gauss_bound_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.NormFormGaussBound.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | exact GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound <;> assumption)
