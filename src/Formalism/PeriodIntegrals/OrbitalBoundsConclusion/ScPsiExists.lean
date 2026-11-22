module

public import Mathlib
public import Formalism.PeriodIntegrals.ScPsiExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

@[expose] public section

theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
