module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGGfStep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGRadProper
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGParamSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH_SFG_PtSmooth

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem slice_family_good : CutSH.SliceFamGood :=
  CutSH.cutSH_sliceFamGood_of CutSH.SFG.gram_function_induction CutSH.SFG.radial_proper
    CutSH.SFG.parameter_smooth CutSH.SFG.point_smooth

end Formalism.FourierDecayAlt.P
