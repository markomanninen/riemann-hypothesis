module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.SkipOneEqSuccAbove

@[expose] public section

theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat :=
  PI.QnCovHatW.qnCovHat_of_lin
