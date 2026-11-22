module

public import Mathlib
public import Formalism.PeriodIntegrals.LocProdFormula
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ProdFormulaE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalProductFormula.LocProdFormulaOf

@[expose] public section

theorem local_product_formula : PI.LocProdFormula :=
  PI.LocProdFormulaW.locProdFormula_of product_formula_e
