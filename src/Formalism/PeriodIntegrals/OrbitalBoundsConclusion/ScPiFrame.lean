module

public import Mathlib
public import Formalism.PeriodIntegrals.ScPiExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight

@[expose] public section

theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
