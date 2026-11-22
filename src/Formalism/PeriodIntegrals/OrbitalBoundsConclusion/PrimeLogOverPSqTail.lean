module

public import Mathlib
public import Formalism.PeriodIntegrals.PrimeSums
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogDivSqLeDiv

@[expose] public section

theorem prime_log_over_sq_tail : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
