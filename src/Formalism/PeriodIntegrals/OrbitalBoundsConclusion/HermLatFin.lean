module

public import Formalism.PeriodIntegrals.HermLatFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HermLatFinMain

@[expose] public section

theorem hermitian_lattice_finite : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
