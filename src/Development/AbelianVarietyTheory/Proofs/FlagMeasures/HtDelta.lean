module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodModKLocalGen

@[expose] public section

namespace GlobalTheory.DiffModProd

theorem htDelta : Formalism.L2.SG.NGHTie.HTDelta := by
  unfold Formalism.L2.SG.NGHTie.HTDelta
  exact finprod_modK_localGen

end GlobalTheory.DiffModProd
