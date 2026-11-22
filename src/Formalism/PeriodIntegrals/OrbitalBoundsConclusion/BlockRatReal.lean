module

public import Mathlib
public import Formalism.PeriodIntegrals.BlockRatReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.NuOfAntitone
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.MapDetGenM

@[expose] public section

theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
