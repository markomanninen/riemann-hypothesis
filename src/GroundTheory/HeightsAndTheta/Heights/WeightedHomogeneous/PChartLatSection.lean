module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]



end ChartLatSection


end

end GroundTheory.Heights₂.Heights
