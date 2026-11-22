module

public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima

@[expose] public section

namespace GlobalTheory

theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
