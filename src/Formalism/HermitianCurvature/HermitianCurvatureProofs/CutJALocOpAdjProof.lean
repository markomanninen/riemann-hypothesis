module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_operator_transfer_holds : JALocOp :=
  jALocOp_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds LT.theta_transfer_apply_holds

theorem jALocAdj_of_adjComm (h : FFS.AdjComm) : JALocAdj :=
  jALocAdj_of_tools LT.operator_in_class_holds LT.agreement_on_domain_holds (LT.thetaJ_of_adjComm h)

end Formalism.FourierDecayAlt.P.CutMP.JA

end
