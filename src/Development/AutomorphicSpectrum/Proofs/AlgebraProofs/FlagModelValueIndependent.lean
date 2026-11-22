module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelValueIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairValueIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelCommonModel
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ImportsAlt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinVerticalDivisorStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.JoinTwoModels
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeftStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRightStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagPlainValueIndependentStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagFurtherTermIndependentStatementStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.FlagModelValue


open GroundTheory.Heights₂.Heights.NumbersDVR in
theorem main : FlagModelValueIndependence.Statement :=
  FlagModelValueIndependence.proof
    (FlagPairValueIndependence.proof GlobalTheory.T.flag_plain_value_independent GlobalTheory.T.flag_further_term_independent_statement)
    (_root_.GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelCommonModel.proof
      GlobalTheory.CompanionTheory.CommAlg.joinTwoModels
      GlobalTheory.CompanionTheory.CommAlg.JoinPullbackAlt.main
      GlobalTheory.CompanionTheory.Heights.join_vertical_divisor_statement
      GlobalTheory.T.flag_model_join_left GlobalTheory.T.flag_model_join_right)

end GlobalTheory.CompanionTheory.CommAlg.FlagModelValue
