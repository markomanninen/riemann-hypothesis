module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev muInf (X : CData) : Measure X.I.Ginf := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)

end Formalism.MainNotions.LeviCoordinates

end
