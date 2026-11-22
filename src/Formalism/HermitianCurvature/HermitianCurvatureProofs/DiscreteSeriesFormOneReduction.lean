module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

end Formalism.FourierDecayAlt.P.DDSmoothness

namespace Formalism.FourierDecayAlt.P

theorem discrete_series_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side

end Formalism.FourierDecayAlt.P
