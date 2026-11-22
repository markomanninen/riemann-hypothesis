module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthTwoGeneratorQuotient

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem lengthFormulaDimTwo : LengthFormulaDimTwo.Statement.{u} :=
  ReciprocityTheory.ChartRestriction.G.AI.length_two_generator_quotient

end GroundTheory.Heights₂.Heights.NumbersDVR
