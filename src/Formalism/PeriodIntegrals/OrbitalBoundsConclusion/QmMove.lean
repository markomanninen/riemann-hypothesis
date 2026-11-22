module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermsSignSquared

@[expose] public section

theorem quantum_minor_move : PI.QmMove := ⟨PI.UnitaryGroupMassFormula.QmMove.move_operator_vector, PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance⟩
