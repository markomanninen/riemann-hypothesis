module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne

@[expose] public section

namespace PI.WBL.NIS

theorem measSideP : MeasSideP := by
  intro k r z u Wp _ _ _ π μW μN hz hT hπ hW hN
  exact Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN

theorem normIdSm_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) : Formalism.FourierDecayAlt.ThreeDimData.NormIdSm :=
  normIdSm_of hGS hGG measSideP

end PI.WBL.NIS
