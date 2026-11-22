module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AssembleL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FwdEx

@[expose] public section

namespace Formalism.L2.SG.LocalCountModules

theorem localCountZeroLocal_holds : Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.locCnt0L_of_fwd Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic.fwdEx

end Formalism.L2.SG.LocalCountModules
