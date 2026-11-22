module

public import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

@[expose] public section

namespace Formalism.HermitianLatticeCounting.Final.S4

theorem weightedCS : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz
theorem omCount : Formalism.HermitianLatticeCounting.S4.OmCount := Formalism.HermitianLatticeCounting.P.orbit_count_formula
theorem step4 : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.Final.S4
