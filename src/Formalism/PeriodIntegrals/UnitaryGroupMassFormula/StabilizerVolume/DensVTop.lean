module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll

@[expose] public section

namespace PI.VolStabS

theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabS
