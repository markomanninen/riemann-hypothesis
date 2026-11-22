module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantDeterminantScaling.IntCastMulEqSmul

@[expose] public section

theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet :=
  PI.QnCovDetW.qnCovDet_of_lin
