module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerProductCast.OfFnProdIntCast
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

@[expose] public section

theorem quantum_minor_star : PI.QmStar :=
  PI.UnitaryGroupMassFormula.QmStar.qmStar_of quantum_minor_row_form
