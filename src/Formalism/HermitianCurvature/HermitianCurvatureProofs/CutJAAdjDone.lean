module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdjProof
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjJComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem local_adjoint_transfer_holds : JALocAdj := jALocAdj_of_adjComm FFS.adjoint_commutation_holds

theorem local_class_transfer_holds : JALocCC := jALocCC_of_op local_operator_transfer_holds local_adjoint_transfer_holds

theorem group_action_commutation_holds : GA.GAJComm := GA.gAJComm_of_adjComm FFS.adjoint_commutation_holds

theorem group_adjoint_transfer_holds : JAGroupAdj := jAGroupAdj_of_jComm group_action_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
