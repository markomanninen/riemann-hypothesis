module

public import Mathlib
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylConjugationFixedColumn.ReflectionScalarDualIsotropic

@[expose] public section

theorem weyl_level_element_properties' : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts :=
  PI.IsotropicReflections.isotropic_reflection_properties
