module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHChk

@[expose] public section

namespace Formalism.FourierDecayAlt.P5.HerD

theorem thmPActualCpt_of_stepExp0 (h0 : StepExp0) : ThmPActualCpt :=
  theorem_P_compact_of_step_density Formalism.FourierDecayAlt.P.level_transport_hermitian h0

end Formalism.FourierDecayAlt.P5.HerD
