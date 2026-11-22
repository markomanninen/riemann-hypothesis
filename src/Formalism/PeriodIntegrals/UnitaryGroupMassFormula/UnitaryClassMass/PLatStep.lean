module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LsLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSLocA

@[expose] public section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem lattice_modification : LatStep := latStep_of_parts lsLat lsOne lsLoc

end PI.UnitaryGroupMassFormula.UJClassMass
