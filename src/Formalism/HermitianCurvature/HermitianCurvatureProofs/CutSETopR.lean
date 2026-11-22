module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpecAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSQQAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSXiTest
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPairDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_TopSpec

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_R (hR : RDSOpR) (hRv : RDSOpRv) : RDIdentSpec :=
  rDIdentSpec_of_open spectral_operator_A_adjoint hR hRv spectral_operator_A spectral_pairing_adjoint spectral_quadratic_adjoint spectral_xi_test spectral_pairing_identity

theorem thmPActualCpt_of_R (hR : RDSOpR) (hRv : RDSOpRv) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_spec (rDIdentSpec_of_R hR hRv)

end Formalism.FourierDecayAlt.P.CutSE
