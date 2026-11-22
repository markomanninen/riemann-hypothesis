module

public import Mathlib
public import Formalism.PeriodIntegrals.BetaLUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.BetaLUniqOfAnisoEigen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.EigenvalueLastLineOne

@[expose] public section

theorem beta_l_unique : PI.BetaLUniq :=
  PI.UnitaryGroupMassFormula.BetaLUniq.betaLUniq_of_aniso_eigen PI.UnitaryGroupMassFormula.BetaLUniq.weight_space_anisotropic
    PI.UnitaryGroupMassFormula.BetaLUniq.eigenvalue_last_line_eq_one
