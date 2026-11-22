module

public import Mathlib
public import Formalism.PeriodIntegrals.ContractionsCovariantIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.QnCovHat2OfLin

@[expose] public section

theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := PI.QnCovHat2W.qnCovHat2_of_lin
