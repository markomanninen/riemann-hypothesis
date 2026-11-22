module

public import Formalism.PeriodIntegrals.PrimeSums
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop

@[expose] public section

theorem sum_log_p_over_p : PI.PrimeLogOverP := PI.PrimeLogOverPWork.sum_log_div_prime_le
