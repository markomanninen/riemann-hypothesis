module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.VanishInvertible
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Decomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Derived

@[expose] public section

theorem productFramesDense_holds : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep

theorem unitaryGroupDense_holds : PI.UnitaryDense := unitaryDense_of productFramesDense_holds
