module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JConvOfJDom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CellSmoothness

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem jf_jDom_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)

theorem jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom (jf_jDom_of_nnMaj h)

end Formalism.FourierDecayAlt.P
