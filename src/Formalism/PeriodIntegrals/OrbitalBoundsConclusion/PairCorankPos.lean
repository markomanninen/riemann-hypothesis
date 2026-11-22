module

public import Mathlib
public import Formalism.PeriodIntegrals.PairCorankPos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe

@[expose] public section

theorem pair_corank_pos : PI.PairCorankPos.CorankPosG := PI.PairCorankPos.W.corankPosG
