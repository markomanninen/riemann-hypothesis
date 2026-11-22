module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTop

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem head_top : KB.HeadTop := pb_headTop_of_mkTop top_truncation_of_averages

end Formalism.FourierDecayAlt.P
