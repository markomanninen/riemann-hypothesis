module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfRatIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfModGOfAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFrameCong

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem term_carrier_holds : TermCarC :=
  termCarC_of rational_isomorphism_holds reduction_mod_g_holds frame_congruence_holds

end Formalism.L2.SG.Pf.RegroupPf
