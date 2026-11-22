module

public import Mathlib
public import Formalism.PeriodIntegrals.WeakApproxDVR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExistenceHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.RhoProjectionAssembly

@[expose] public section

theorem weak_approximation_dvr : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
