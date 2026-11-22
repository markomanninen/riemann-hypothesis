module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

@[expose] public section

theorem quantum_minor_row_expansion : PI.QmRowExp := PI.qmRowExp_of_rowForm quantum_minor_row_form
