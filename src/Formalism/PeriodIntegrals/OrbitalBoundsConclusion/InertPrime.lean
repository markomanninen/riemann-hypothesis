module

public import Mathlib
public import Formalism.PeriodIntegrals.InertPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi

@[expose] public section

open NumberField

theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
