module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_base_pair_eq_module_product : Formalism.L2.SG.NGHTie.HTPlace := by
  first | exact @GlobalTheory.HTPlaceLeaf.htPlace | exact GlobalTheory.HTPlaceLeaf.htPlace | (intros; apply GlobalTheory.HTPlaceLeaf.htPlace <;> assumption)
