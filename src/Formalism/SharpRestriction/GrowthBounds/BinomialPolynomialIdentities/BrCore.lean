module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
end B1

section B2
end B2

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

end Mod

section B6
end B6

end Formalism.MainNotions.G.ColumnFamilies
