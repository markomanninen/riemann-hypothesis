module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.UniformIntegrabilityProportionalityHolds
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsProjFullRankMeetsRegular
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegralPoints
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHoldsStatement

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar

theorem chartDivisorCompare : GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.Statement :=
  @GroundTheory.Heights₂.Heights.Targets.ChartDivisorCompare.proof GlobalTheory.T.segre_chart_integral_holds
    GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints.proof
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorComponents
    GroundTheory.Heights₂.Heights.AutoClose.Targets_ChartDivisorLength

end GlobalTheory.CompanionTheory.Ar
