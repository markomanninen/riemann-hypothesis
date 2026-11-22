module

public import Mathlib
public import Formalism.PeriodIntegrals.LatDefs
public import Formalism.PeriodIntegrals.AreaLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo

@[expose] public section

theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
