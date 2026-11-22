module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishMain

@[expose] public section

theorem operator_words_bound : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
