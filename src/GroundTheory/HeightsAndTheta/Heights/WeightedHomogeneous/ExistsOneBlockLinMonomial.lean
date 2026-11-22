module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (IsMultiHomog IsArithVar mCoordIdeal secM MRing MRingOver)

noncomputable section

section Values

variable {K : Type} [Field K] {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (i : ℕ)

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
