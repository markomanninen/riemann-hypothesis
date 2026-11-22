module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerLatticeCoordinatesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm

@[expose] public section

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

theorem covolOne3C_holds : Formalism.L2.SG.Pf.VolPinAsm.CovolOne3C :=
  covolOne3C_of Formalism.L2.S.Pv.Chart.chartC_holds (stabilizerLatticeCoordinates_of Formalism.L2.SG.LatBAsm.stabilizer_lattice_twisted_prod)

end Formalism.L2.SG.NGCut.StabilizerCovolume
