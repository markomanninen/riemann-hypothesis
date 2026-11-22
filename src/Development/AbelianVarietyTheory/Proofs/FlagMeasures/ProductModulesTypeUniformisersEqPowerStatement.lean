module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPower
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_modules_type_uniformisers_eq_power : Formalism.L2.SG.NGHTie.HTTheta := by
  first | exact @GlobalTheory.HTThetaLeaf.main | exact GlobalTheory.HTThetaLeaf.main | (intros; apply GlobalTheory.HTThetaLeaf.main <;> assumption)
