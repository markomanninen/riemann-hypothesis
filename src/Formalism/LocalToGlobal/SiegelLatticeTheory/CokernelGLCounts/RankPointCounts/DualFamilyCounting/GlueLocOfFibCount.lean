module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization

@[expose] public section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.G6

theorem glueLoc_of_fibCount (hn : FibCount) : GlueLoc :=
  glueLoc_of projection_into_holds (projOnto_of summand_localization riesz_hermitian_holds) hn

end Formalism.L2.SG.Pf.Cnt
