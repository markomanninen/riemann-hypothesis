module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviWFin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfSratZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviPos

@[expose] public section

namespace Formalism.L2.SG.Pf.SlabCount

theorem leviFinC_of_pos (hP : LeviPosC) : LeviFinC :=
  leviFinC_of (leviStabFinC_of (leviWFinC_of hP) rational_z_condition_holds)

theorem levi_finite_index : LeviFinC :=
  leviFinC_of_pos levi_totally_positive_definite

end Formalism.L2.SG.Pf.SlabCount
