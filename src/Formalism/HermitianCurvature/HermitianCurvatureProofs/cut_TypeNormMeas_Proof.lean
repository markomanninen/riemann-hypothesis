module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasMain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_TypeNormMeas_TC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasHM

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

theorem type_norm_measurability_holds : TDM.TypeNormMeas :=
  TNM.typeNormMeas_of_typeComm_houseMeas TNM.type_commutation_holds TNM.HM.householder_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP
