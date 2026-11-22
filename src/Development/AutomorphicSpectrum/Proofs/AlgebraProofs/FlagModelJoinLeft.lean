module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof GlobalTheory.T.pair_number_pullback
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
