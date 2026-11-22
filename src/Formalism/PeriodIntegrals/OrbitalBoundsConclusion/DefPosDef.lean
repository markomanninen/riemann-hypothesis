module

public import Mathlib
public import Formalism.PeriodIntegrals.FinOrdAd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.SplittingOfExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.PositiveDefiniteSecond

@[expose] public section

theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
