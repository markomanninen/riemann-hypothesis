module

public import Mathlib
public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantLinearProduct.OfFnProdSmul

@[expose] public section

theorem covariant_linear : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
