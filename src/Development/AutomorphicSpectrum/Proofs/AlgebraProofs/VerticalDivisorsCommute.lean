module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisorStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem verticalDivisorsCommute : VerticalDivisorsCommute.Statement.{0} :=
  VerticalDivisorsCommute.proof GlobalTheory.T.cut_effective_divisor Representative.full
    IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full
    SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full
    DimStrictDrop.full

end GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors
