module

public import Mathlib
public import Formalism.PeriodIntegrals.SymDist
public import Formalism.PeriodIntegrals.ExpTri
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf

@[expose] public section

theorem symDist_of : PI.ExpTri → PI.SymDist := PI.SymDistWork.symDist_of
