module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem frame_existence : FrameEx := fun _ _ _ hz hT => Qx8.frame_exists hz hT

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
