module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPermOfMin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExpOf

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem glueProd_of_iso (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp) :
    GlueProd := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos M hM Λ₀ hΛ₀ T hT
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs (nondegenerate_of hs hnd)
        hΛ₀.1 hΛ₀.2.1 }
  refine ⟨⟨genus_of_fib h1 h2 h6 hI hK hF hs hnd hUc hpos hM hΛ₀ hT, fun hg 𝔭 h𝔭 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hg h𝔭⟩, card_glue hK hF hUc hM hΛ₀ hΛ₀full hT⟩

end Formalism.L2.SG.Pf.G8

namespace Formalism.L2.SG.Pf.Cnt

theorem glueProd_of (h1 : JordanExists) (h2 : JordanInv) (h3 : JordanIsom) (h6 : GlueLoc) : GlueProd :=
  G8.glueProd_of_iso h1 h2 h6 (G8.isomFixOfExp_of h3)

end Formalism.L2.SG.Pf.Cnt
