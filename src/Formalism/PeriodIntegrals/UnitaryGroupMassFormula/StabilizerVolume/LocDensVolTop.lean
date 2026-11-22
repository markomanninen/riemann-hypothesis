module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSAInt

@[expose] public section

namespace PI.VolStabS

open VolAAW

theorem volAA_of_chInf (hC : ChInf) : VolAA :=
  volAA_of (condAA_of (condExact_of sAf_holds hC))

theorem volAA_of_lift (hL : ChLift) : VolAA :=
  volAA_of_chInf (chInf_of_lift hL)

end PI.VolStabS
