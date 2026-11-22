module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMain
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApproxFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMem

@[expose] public section

namespace Formalism.L2.SG.TermOp.Vanish

theorem rational_cocompact_holds : RCocompactC := rCocompactC_of ratApprox_holds ratMem_holds

end Formalism.L2.SG.TermOp.Vanish
