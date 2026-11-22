module

public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly

@[expose] public section

namespace PositivityTheory.EqVol

theorem sa : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := GroundTheory.Heights₂.Heights.StrongApprox.SAHolds.full

theorem saOpen : ReciprocityTheory.ChartRestriction.G.SA.SAOpenStatement := GroundTheory.Heights₂.Heights.StrongApprox.SAOpenHolds.full

end PositivityTheory.EqVol
