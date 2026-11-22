module

public import Mathlib
public import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM

@[expose] public section

theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
