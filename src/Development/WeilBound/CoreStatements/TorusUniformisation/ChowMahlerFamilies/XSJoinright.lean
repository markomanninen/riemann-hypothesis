module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinRight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumRelabel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalComponentFibre
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement

@[expose] public section

namespace PositivityTheory.Xgn.A_s_joinright

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.full GenericDimBound.full GenericDimGe.proof SpecialIdealCorresp.full
    SpecialIdealMultiHomog.full SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialQuotDim.full
    ComponentDim.proof

theorem pairNumRelabel : PairNumberRelabelAlt.Statement :=
  PairNumberRelabelAlt.proof (VerticalComponentFibre.proof fibreVarieties)

theorem of_pullback (h : PairNumberPullback.Statement) : FlagModelJoinRightAlt.Statement :=
  FlagModelJoinRightAlt.proof JoinVerticalDivisor.proof (FlagPairJoinRight.proof JoinVerticalDivisorRight.proof)
    (PairNumberJoinRight.proof
      (PairNumberJoinLeft.proof h JoinVerticalDivisorLeft.proof BirationalJoin.proof)
      JoinVerticalDivisorRight.proof pairNumRelabel)

end PositivityTheory.Xgn.A_s_joinright
