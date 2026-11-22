module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds

@[expose] public section

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

theorem NmlInv_holds : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv :=
  nmlInv_of NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds NmlSep_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
