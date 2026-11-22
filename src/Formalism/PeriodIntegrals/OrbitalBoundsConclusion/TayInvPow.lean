module

public import Formalism.PeriodIntegrals.TayInvPow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TaylorInversePower.SumMultinomialSub

@[expose] public section

theorem coeffInversePowerFacts.{u, v} : PI.TayInvPow.{u, v} := PI.UnitaryGroupMassFormula.TayInvPow.main
