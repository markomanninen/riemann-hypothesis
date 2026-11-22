module

public import Mathlib
public import Formalism.PeriodIntegrals.AdBridgeSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift

@[expose] public section

theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
