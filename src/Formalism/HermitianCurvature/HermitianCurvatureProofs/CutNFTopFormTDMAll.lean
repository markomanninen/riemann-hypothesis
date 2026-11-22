module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMSE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMVV
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMDop

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

theorem topDMeasCpt_of_typeNormMeas (h : TypeNormMeas) : TopDMeasCpt :=
  topDMeasCpt_of_parts h vector_positive_cone diff_operator_in_class_CC scalar_point_measurability_holds empty_list_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP.TDM
