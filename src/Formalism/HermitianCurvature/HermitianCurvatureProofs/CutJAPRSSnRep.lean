module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDone

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_jf (hJ : JfSmoothDS) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_polyS hJ JA.SSn.Rep.Core.TC.PR.polynomial_radial_holds

end Formalism.FourierDecayAlt.P.CutMP
