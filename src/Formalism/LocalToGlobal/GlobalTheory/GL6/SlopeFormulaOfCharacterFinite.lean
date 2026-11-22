module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.SlopeRamifiedInducedPrimeField
public import Formalism.LocalToGlobal.GlobalTheory.GL6.MetricDisjointSupportOrthogonal
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PolynomialFunctionFrameTranslate
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

theorem slope_formula_of_isometry {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_diamonds hS Tf hA (diamond_elements_exist_all Tf) (metric_disjoint_support_orthogonal Tf) hI

theorem slope_formula_of_character_finite {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hC : ChiFin Tf)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_isometry hS Tf hA (diamond_isometry_at_infinity Tf hC hA)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
