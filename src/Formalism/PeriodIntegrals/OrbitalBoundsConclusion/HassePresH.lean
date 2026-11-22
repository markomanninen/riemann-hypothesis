module

public import Formalism.PeriodIntegrals.HassePresH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseDerivativeFiltration.HasseMemHfr

@[expose] public section

theorem hasse_presentation : PI.HassePresH := PI.UnitaryGroupMassFormula.HassePresH.main
