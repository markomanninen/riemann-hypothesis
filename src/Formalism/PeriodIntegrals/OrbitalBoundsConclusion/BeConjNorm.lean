module

public import Mathlib
public import Formalism.PeriodIntegrals.BeConjNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.BeConjNormOfIntInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.MemIntegerRingIffNormLeOne

@[expose] public section

theorem conjugate_norm_bound : PI.BeConjNorm.BeConjNorm :=
  PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic
