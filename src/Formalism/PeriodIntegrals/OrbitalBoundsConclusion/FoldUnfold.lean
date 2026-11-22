module

public import Mathlib
public import Formalism.PeriodIntegrals.FoldUnfold
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain

@[expose] public section

theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
