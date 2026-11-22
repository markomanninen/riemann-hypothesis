module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRRest
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecomp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPWordAsm

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem polynomial_radial_holds : PolyRadialS := polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
