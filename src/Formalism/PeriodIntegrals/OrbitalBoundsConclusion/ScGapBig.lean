module

public import Mathlib
public import Formalism.PeriodIntegrals.ScGapBig
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain

@[expose] public section

theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
