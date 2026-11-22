module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralSobolevSecondOrder
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSMeas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSWordNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JslHsInnerSelfNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeibnizClsC

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem jSliceGenC_of_radLoc (hR : JSRadLoc) : JSliceGenC :=
  jSliceGenC_of_sob2_meas_locality spectral_sobolev_second_order spectral_measurability (jSL2Loc_of spectral_word_normal_form hR)

theorem leibnizCls_of_radLoc (hR : JSRadLoc) : LeibnizCls :=
  leibnizCls_of_jSliceC (jSliceGenC_of_radLoc hR)

theorem densSmoothCls_of_radLoc (hR : JSRadLoc) : DensSmoothCls :=
  densSmoothCls_of_jSliceC (jSliceGenC_of_radLoc hR)

end Formalism.FourierDecayAlt.P.CutSE
