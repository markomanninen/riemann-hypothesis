module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VENatEqZero

@[expose] public section

namespace GlobalTheory.HTThetaLeaf

theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
