module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegreChartIntegralHolds
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_integral_holds : GroundTheory.Heights₂.Heights.SegreChartIntegral.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | exact GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.Chart.SegreChartIntegral <;> assumption)
