module

public import Mathlib
public import Formalism.PeriodIntegrals.PrimeCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.ChebyshevPrimeBoundsLogFact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.CountSuccLe

@[expose] public section

theorem prime_count_bound : PI.PrimeCountBound :=
  PI.PC.primeCountBound_of 131072 (PI.PC.pcLarge_of PI.PC.psiUpperBound_holds) PI.PC.pcSmall
