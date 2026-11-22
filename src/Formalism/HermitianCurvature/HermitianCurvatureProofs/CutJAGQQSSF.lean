module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFBridge
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFSS

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem quadratic_second_shift_form : SSn.Rep.Core.GQQSSF :=
  SSn.Rep.Core.GQ.gQQSSF_of_cut SSn.Rep.Core.GQ.quadratic_transfer_identity SSn.Rep.Core.GQ.quadratic_kappa_identity SSn.Rep.Core.GQ.quadratic_shift_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
