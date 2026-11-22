module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBasisHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleyAlgebraicHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleySmoothnessHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDomainIsDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeActionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolLevi

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_chart_holds : GChart := gChart_of lie_basis_holds cayley_algebraic_holds group_vector_space cayley_smoothness_holds

theorem unitary_capelli_holds : UCap := uCap_of positive_domain_is_domain right_type_action_holds left_type_action_holds

theorem jfSmoothBuilt_of_rest (hN : NDiff) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hE : ChartEqs) (hR : EllRegW) :
    JfSmoothBuilt :=
  jfSmoothBuilt_of_leaves hN unitary_capelli_holds hP hC group_chart_holds hE classical_to_weak_solution hR JfS.symbol_nilpotent_holds lie_stabilizer_splitting

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
