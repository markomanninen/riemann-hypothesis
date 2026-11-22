module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableRhoUni
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableFormAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjIntAsm

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

theorem adjoint_integral_identity_holds : AdjInt := adjInt_of_parts hermitian_curvature_adjoint_integral unitary_rho_holds form_adjoint_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
