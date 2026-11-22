module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem positive_domain_is_domain : IsDomOmPlus := fun _ _ _ _ hz hz' =>
  Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus hz hz'

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
