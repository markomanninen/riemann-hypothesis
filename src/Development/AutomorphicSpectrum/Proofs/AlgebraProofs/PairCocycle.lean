module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem pairCocycle : PairCocycle.Statement :=
  PairCocycle.proof GlobalTheory.T.flag_independence GlobalTheory.T.vertical_divisors_commute IntNumAddFirst.full

end GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed
