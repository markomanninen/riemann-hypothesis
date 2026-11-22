module

public import Formalism.PeriodIntegrals.AdelClassFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.AdelClassFinOfSvReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorReal

@[expose] public section

theorem adelic_class_set_finite : PI.AdelClassFin.AdelClassFin :=
  PIW.AdelClassFin.adelClassFin_of_svReal PIW.AdelClassFin.successive_vector_real
