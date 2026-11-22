module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.SubQuotient.proof GlobalTheory.T.flag_independence

end GlobalTheory.CompanionTheory.Ar.Num.SubQuotFlags
