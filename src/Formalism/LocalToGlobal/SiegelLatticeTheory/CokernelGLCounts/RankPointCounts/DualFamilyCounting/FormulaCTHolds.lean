module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame

@[expose] public section

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaCT_holds : FormulaCT := formulaCT_of DualityBasisChange.frameBasisL_holds

end Formalism.L2.SG.Pf.Cnt
