module

public import Mathlib
public import Formalism.PeriodIntegrals.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.MeasureIsomorphismAtInfinity

@[expose] public section

theorem split_row_iso : PI.SplitRow.SplitRow := PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity
