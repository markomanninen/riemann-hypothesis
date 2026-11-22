module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.EqZeroOfMemNbhdA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

@[expose] public section

namespace PI.VolStabS

theorem discHF_holds : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)

theorem exFDStab_holds : ExFDStab := exFDStab_of scha_holds discHF_holds

end PI.VolStabS
