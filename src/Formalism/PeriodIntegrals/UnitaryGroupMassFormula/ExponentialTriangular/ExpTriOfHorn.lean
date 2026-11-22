module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SpecExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.PsumEqRange

@[expose] public section

namespace PI.ET

theorem expTri_of_horn (hH : Horn) : PI.ExpTri :=
  expTri_of specExists hsEq hH abelSq euclTri

end PI.ET
