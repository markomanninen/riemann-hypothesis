module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensChLift

@[expose] public section

namespace PI.VolStabS

theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabS
