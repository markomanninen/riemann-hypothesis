module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem nonvanishing_coefficient_positivity : NonvanishingCoefficientPositivity (E := E) := CoefficientPositivity.nonvanishing_coefficient_positivity_of unipotent_lattice_lift fourier_coefficients_holds

end ReciprocityTheory.ChartRestriction.G.FD
