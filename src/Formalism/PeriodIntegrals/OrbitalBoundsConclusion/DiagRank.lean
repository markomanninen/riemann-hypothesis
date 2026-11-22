module

public import Mathlib
public import Formalism.PeriodIntegrals.DiagRank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe

@[expose] public section

theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
