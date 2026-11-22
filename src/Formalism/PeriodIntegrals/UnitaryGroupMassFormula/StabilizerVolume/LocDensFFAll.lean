module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFIn

@[expose] public section

namespace PI.VolStabS

theorem fFCount_holds : FFCount := fFCount_of_inert FFHS.fFInert_holds

end PI.VolStabS
