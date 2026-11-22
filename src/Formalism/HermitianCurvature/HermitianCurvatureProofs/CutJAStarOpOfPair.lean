module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpModelAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpFundQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecFinal

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAStarOp_of_pairL (h : SA.SAPairL) : JAStarOp :=
  SA.jAStarOp_of_parts SA.model_adjoint_identity_holds self_adjoint_section_holds h SA.fundamental_quadratic_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
