module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCountPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCount : GroundTheory.Heights₂.Heights.IsolatedPointsCount.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCount.proof GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime
