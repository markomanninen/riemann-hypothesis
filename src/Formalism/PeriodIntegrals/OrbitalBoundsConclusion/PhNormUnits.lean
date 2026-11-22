module

public import Mathlib
public import Formalism.PeriodIntegrals.PhNormUnits
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation

@[expose] public section

theorem phase_norm_units : PI.PhNormUnits.Target := PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_of_calculation
