module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatBdd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundedOperatorsSquareIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAIsAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JAAssembleQQ : Prop :=
  JDHatOpQQ → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOpQQ → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTrQQ

theorem jAdjTrQQ_of_leaves (hA : JAAssembleQQ) (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp)
    (h12 : JAGroupAdj) (h13 : JALocCC) (h14 : JAFFStable) : JAdjTrQQ :=
  hA h1 hat_bounded_decay_holds transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable h7 transfer_star_bound_holds transfer_is_adjoint_holds phi_operator_transfer_holds h11
    h12 h13 h14

end

end Formalism.FourierDecayAlt.P.CutMP.JA
