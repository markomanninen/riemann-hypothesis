module

public import Formalism.PeriodIntegrals.SchurFock
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.SchurFockOf

@[expose] public section

theorem schur_fock : PI.SchurFock := PI.WSF.schurFock_of highest_weight_irreducible
