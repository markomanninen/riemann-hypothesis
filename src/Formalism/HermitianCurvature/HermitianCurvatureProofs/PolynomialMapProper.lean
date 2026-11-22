module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

@[expose] public section

theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
