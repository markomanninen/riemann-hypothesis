module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXKS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCV

@[expose] public section

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem coordCovol_of (hL : KapLaw) (hN : NOfib) (hB : BlockCovol) : Formalism.L2.SG.Pf.LsNc5.CoordCovol :=
  coordCovol_of_cut hL kapSurj_holds hN hB (fun X u => cVal_prod X u)

end Formalism.L2.SG.Pf.NcReal.JX
