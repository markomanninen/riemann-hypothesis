module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableEquivOps

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAFFStable_of_adjComm (hA : AdjComm) : JAFFStable :=
  jAFFStable_of_parts germ_operators_holds extension_locality_holds smooth_operators_holds hA equivariant_operators_holds positive_domain_condition_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
