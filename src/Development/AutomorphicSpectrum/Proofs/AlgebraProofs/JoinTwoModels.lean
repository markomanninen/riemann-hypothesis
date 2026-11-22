module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerSide
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg

theorem joinTwoModels : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

end GlobalTheory.CompanionTheory.CommAlg
