module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.FockJointMultOfCauchy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyFin

@[expose] public section

theorem fock_joint_multiplicity : PI.FockDegreeTwoParts.JointMult := PI.FJM.fockJointMult_of_cauchy PI.FJM.cauchy_highest_weight
