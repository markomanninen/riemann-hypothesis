module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SelfAdjointDescentHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecRad
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecCover
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecAsm

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_section_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SA.SASection :=
  Formalism.FourierDecayAlt.P.CutMP.JA.SA.sASection_of_parts Formalism.FourierDecayAlt.P.CutMP.JA.SA.radial_section_holds
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
