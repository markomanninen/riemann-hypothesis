module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOneLetterDens
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceDone
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfSpectralData

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem leibniz_class : LeibnizCls := leibnizCls_of_radLoc spectral_radial_locality

theorem density_smooth_class : DensSmoothCls := densSmoothCls_of_radLoc spectral_radial_locality

theorem thmPActualCpt_of_spec (h : RDIdentSpec) : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  thmPActualCpt_of_leaves (one_letter_density_estimate leibniz_class density_smooth_class) density_smooth_class
    (radDecay_of_spec h)

end Formalism.FourierDecayAlt.P.CutSE
