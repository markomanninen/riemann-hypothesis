module

public import Mathlib
public import Formalism.PeriodIntegrals.FglGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Expand

@[expose] public section

theorem phase_gram' : PI.FglGram.PhGram :=
  PI.UnitaryGroupMassFormula.PhGram.phGram_of_steps PI.UnitaryGroupMassFormula.PhGram.gram_bilinear_expansion PI.UnitaryGroupMassFormula.PhGram.gram_sum_first_variable
