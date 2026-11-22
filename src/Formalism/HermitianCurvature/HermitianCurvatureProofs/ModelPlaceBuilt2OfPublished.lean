module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentDerivative
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupEquationsPostHolds
public import Mathlib
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Moments
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRSSnRep

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem jfSmoothBuilt_of_chart (hE : ChartEqs) (hR : EllRegW) : JfSmoothBuilt :=
  jfSmoothBuilt_of_rest nilpotent_derivative group_equations_post_holds smooth_of_coefficients_holds hE hR

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

namespace Formalism.FourierDecayAlt.P.CutMP

end Formalism.FourierDecayAlt.P.CutMP
