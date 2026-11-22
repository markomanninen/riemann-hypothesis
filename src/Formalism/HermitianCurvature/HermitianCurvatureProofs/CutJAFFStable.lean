module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableOfAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem smooth_forms_stability_holds : JAFFStable := FFS.jAFFStable_of_adjComm FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
