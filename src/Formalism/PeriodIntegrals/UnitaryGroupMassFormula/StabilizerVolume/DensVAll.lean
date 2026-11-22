module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExistsUnifFv

@[expose] public section

namespace PI.VolStabS

theorem densV_holds : DensV :=
  densV_of_gram (gramFilt_of (dxOpen_of secGram_holds))

end PI.VolStabS
