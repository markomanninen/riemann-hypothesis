module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Closed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasureIsomorphismAtInfinity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion

@[expose] public section

theorem infinite_measure_transfer : Formalism.L2.SG.Pf.MeasInf.InfTransfer :=
  Formalism.L2.SG.Pf.MeasInfW.measInfXfer_of Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_recursion Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion
    Formalism.L2.SG.Pf.MeasInfW.nilpotent_measure_closed_form Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_closed_form
