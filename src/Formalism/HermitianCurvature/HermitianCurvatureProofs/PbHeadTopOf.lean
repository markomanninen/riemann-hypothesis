module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfRadialExhaustion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAt

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem pb_headTop_of (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) : KB.HeadTop :=
  head_top_of_radial_exhaustion hU5 hPic head_weight_at

end Formalism.FourierDecayAlt.P
