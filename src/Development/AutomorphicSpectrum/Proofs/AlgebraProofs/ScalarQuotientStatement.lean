module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.proof GlobalTheory.T.flag_independence

end GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags
