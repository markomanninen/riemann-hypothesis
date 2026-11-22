module

public import Mathlib
public import Formalism.PeriodIntegrals.BallQuotLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg

@[expose] public section

theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
