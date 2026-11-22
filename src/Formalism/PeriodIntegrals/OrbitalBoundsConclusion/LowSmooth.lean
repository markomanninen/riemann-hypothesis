module

public import Mathlib
public import Formalism.PeriodIntegrals.LowCyc
public import Formalism.PeriodIntegrals.KFinSmooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

@[expose] public section

theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := PI.UnitaryGroupMassFormula.LowSmooth.lowSmooth_of_kFinSmooth
