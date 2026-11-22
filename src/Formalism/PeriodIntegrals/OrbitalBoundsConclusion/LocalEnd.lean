module

public import Mathlib
public import Formalism.PeriodIntegrals.LocalEnd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IntVal

@[expose] public section

theorem local_endomorphism_homeomorph : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
