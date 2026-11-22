module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | exact GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main <;> assumption)
