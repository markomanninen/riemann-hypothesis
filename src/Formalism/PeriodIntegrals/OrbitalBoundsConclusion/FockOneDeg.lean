module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.SameBlockOfPosC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KernelHarmonic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap

@[expose] public section

theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
