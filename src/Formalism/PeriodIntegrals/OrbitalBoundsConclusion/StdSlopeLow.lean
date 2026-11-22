module

public import Mathlib
public import Formalism.PeriodIntegrals.HookBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaOperatorBasis

@[expose] public section

theorem standard_slope_lower : PI.StdSlopeLow :=
  PI.SlopeSteps.stdSlopeLow_of PI.SlopeSteps.nabla_gram_lower_bound PI.SlopeSteps.gram_matrix_duality
    PI.SlopeSteps.nabla_operator_basis
