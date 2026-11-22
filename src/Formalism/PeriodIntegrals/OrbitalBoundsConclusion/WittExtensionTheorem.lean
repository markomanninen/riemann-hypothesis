module

public import Mathlib
public import Formalism.PeriodIntegrals.WittExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.OneVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.AnisotropicHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.WittOf

@[expose] public section

theorem witt_extension_theorem : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
