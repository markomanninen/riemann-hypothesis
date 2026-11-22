module

public import Mathlib
public import Formalism.PeriodIntegrals.ExpTri
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ProdLeOfInjective

@[expose] public section

theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
