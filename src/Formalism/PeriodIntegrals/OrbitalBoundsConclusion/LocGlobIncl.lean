module

public import Mathlib
public import Formalism.PeriodIntegrals.LocGlobIncl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul

@[expose] public section

namespace PI

theorem local_global_inclusion' : PI.LocGlobIncl := PI.LocGlobInclWork.main

end PI
