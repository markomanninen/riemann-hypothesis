module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting

@[expose] public section

theorem weil_measure_compat : Formalism.L2.SG.Pf.MeasCore.MWCore :=
  PI.UnitaryGroupMassFormula.MeasWCore.measWCore_main
