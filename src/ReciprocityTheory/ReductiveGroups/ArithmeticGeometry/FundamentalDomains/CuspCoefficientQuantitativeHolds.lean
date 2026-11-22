module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitative

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cusp_coefficient_quantitative_holds : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
