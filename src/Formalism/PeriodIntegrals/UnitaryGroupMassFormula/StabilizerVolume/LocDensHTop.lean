module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHIL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVol

@[expose] public section

namespace PI.VolStabS

theorem densAA_of_open (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) : DensAA :=
  densAA_of fibLat_holds fFCount_holds
    (resAA_of hV latFacts_holds hH (idxAA_of idxL_holds hI) hC)

end PI.VolStabS
