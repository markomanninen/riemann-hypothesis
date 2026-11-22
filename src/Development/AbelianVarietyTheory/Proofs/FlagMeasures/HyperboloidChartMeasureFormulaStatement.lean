module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
