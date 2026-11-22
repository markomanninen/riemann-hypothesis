module

public import Mathlib
public import Formalism.PeriodIntegrals.HwFixedLine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightFixedLine.HwFixedLineMain

@[expose] public section

theorem highest_weight_fixed_line : PI.HwFix.HwFixedLine := PI.HwFix.Line.hwFixedLine_main
