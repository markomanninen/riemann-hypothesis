module

public import Mathlib
public import Formalism.PeriodIntegrals.AutLzFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.AutLzFinMain

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem automorphism_lattice_finite (D : Formalism.BasicNotions.D7) : PI.AutLzFinite.AutLzFin D :=
  PI.AutLzFinite.SlopeTestRemainingChoices.autLzFin_main D
