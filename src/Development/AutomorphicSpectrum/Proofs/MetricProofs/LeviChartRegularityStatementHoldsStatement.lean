module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_chart_regularity_statement_holds : GroundTheory.Heights₂.Heights.NineStatements.NbarLeviChartReg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg | exact GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.nbarLeviChartReg <;> assumption)
