module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefCrys
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.CoordBaseChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CoefficientBaseChange.FinrankIInfKerEquiv

@[expose] public section

theorem coefficient_crystal_generation : Formalism.MainNotions.N.GlobalTheory.CoefCrysGen :=
  PI.CoefExt.coefCrysGen_of PI.CoefExt.invBaseChange
