module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialEqSumOfLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiUpperBoundOfLtThirtyMulSixPow

@[expose] public section

namespace PI.PC

theorem psiUpperBound_holds : CHUpper := chUpper_of chebyshevConstantNumeric dUpper sandwich

end PI.PC
