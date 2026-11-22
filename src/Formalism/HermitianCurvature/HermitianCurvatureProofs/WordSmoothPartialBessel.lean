module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBesselInduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem word_smooth_partial_bessel : CutHB.WordSmooth := PartialBesselWordSmoothness.wordSmooth_of proper_left_variables_domain

end Formalism.FourierDecayAlt.P
