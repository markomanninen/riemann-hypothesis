module

public import Mathlib
public import Formalism.PeriodIntegrals.EfRankSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain

@[expose] public section

theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
