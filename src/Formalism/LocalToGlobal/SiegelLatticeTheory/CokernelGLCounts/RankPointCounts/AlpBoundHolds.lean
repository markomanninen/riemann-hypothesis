module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralApproximation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

@[expose] public section

namespace Formalism.L2.SG.IntegralApproximation

theorem AlpBound_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.AlpBound D := alpBoundU D

end Formalism.L2.SG.IntegralApproximation
