module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TrDetPfH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowBlockCovolOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd

@[expose] public section

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

theorem trDetUnimod_holds : TrDetUnimod := TrD.trDetUnimod_of TrD.detHOne_holds

theorem rowBlockCovol_holds : RowBlockCovol := rowBlockCovol_of trDetUnimod_holds

theorem blockCovol_holds : BlockCovol := blockCovol_of rowBlockCovol_holds

end Formalism.L2.SG.Pf.NcReal.JX.CovB
