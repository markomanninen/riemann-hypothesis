module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.PvLocalSelf

@[expose] public section

theorem hecke_product_rule : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), χ.ProductRule :=
  fun _ _ _ χ => PI.HeckeProdW.productRule χ
