module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds

@[expose] public section

namespace GlobalTheory

theorem stepPinExists_and_formNGC :
    Formalism.L2.SG.NGAnalytic.StepPinExists ∧ Formalism.L2.SG.NGVanish.FormNGC :=
  ⟨Formalism.L2.SG.NGPin.stepPinExists, Formalism.L2.SG.Pf.formNGC_holds⟩

end GlobalTheory
