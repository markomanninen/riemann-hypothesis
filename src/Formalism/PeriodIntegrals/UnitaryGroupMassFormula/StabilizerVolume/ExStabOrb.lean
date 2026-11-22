module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.OrbTupFin

@[expose] public section

namespace PI.VolStabS

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabS
