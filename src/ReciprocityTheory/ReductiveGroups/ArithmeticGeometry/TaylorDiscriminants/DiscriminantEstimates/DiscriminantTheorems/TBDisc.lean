module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.UniformDiscreteness.FgOfUnifDiscrete

@[expose] public section

theorem discriminant_of_product_lower : ReciprocityTheory.ChartRestriction.G.TB.DiscOfProdLowerSt :=
  PI.UnitaryGroupMassFormula.TBDisc.discOfProdLower

theorem formalGroup_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.FGOfDiscSt :=
  PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
