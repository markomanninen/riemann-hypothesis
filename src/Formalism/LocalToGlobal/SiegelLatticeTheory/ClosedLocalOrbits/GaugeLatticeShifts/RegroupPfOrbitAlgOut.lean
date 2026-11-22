module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem orbit_algebra_of_stabilizer (hC : TermCarC) (hS : StabNC) : OrbitAlgC :=
  orbitAlgC_of Formalism.L2.SG.Pf.nilradical_conj_level' hC hS

end Formalism.L2.SG.Pf.RegroupPf
