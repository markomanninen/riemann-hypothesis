module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.AvoidP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.EpNontrivial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeEquality.CoreFgOfLe

@[expose] public section

theorem eq_iff_locallyEq : PI.LocLatEq.Stmt :=
  PI.LocLatEq.W.locLatEq_of PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP
    (PI.LocLatEq.W.coreP_of_unitP_avoidP_intP PI.LocLatEq.W.unitP PI.LocLatEq.W.avoidP PI.LocLatEq.W.intP)
