module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibOps
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibBd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibVLin
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_vector_estimate_holds : NFLeibV :=
  nfLeibV_of (nfLeibOps_of leibniz_expansion_holds) leibniz_bound_holds vector_linearity_holds

end Formalism.FourierDecayAlt.P.CutBP
