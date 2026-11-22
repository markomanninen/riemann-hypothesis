module

public import Mathlib
public import Formalism.PeriodIntegrals.LevelKSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfHL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergParabolicAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviPartAll

@[expose] public section

theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
