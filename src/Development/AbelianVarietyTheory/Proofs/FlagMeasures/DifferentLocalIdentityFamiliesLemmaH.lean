module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HtDelta
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProductStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductModulesTypeUniformisersEqPowerStatement

@[expose] public section

namespace GlobalTheory.HTieLeaf

theorem main : Formalism.L2.SG.FamDefs.HTie :=
  Formalism.L2.SG.NGHTie.hTie_of GlobalTheory.T.local_height_base_pair_eq_module_product GlobalTheory.DiffModProd.htDelta GlobalTheory.T.product_modules_type_uniformisers_eq_power

end GlobalTheory.HTieLeaf
