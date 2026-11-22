module

public import Mathlib
public import Formalism.PeriodIntegrals.NMeasInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula

@[expose] public section

namespace PI

theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
