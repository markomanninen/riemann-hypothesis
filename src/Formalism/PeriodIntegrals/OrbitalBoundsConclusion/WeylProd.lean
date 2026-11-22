module

public import Mathlib
public import Formalism.PeriodIntegrals.WeylProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd

@[expose] public section

theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
