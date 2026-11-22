module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
