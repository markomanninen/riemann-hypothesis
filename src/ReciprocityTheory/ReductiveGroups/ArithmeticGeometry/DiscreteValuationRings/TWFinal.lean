module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out

theorem vRatioGt : VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

theorem tw_of_laws (hL : Laws) (hT : TwistBaseChangeStatement) : TWStatement :=
  tw_of hL.globalFns (twistBCSpan_of hT) vRatioGt

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
