module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasurableSetBorelOfIsClosed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousAtPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfExistSMeasKf

@[expose] public section

namespace PI.LevelKSplit.W.MeasAll

theorem maximal_compact_measurable : PI.LevelKSplit.W.MeasKfAll :=
  PI.LevelKSplit.W.Meas.measKf_of PI.LevelKSplit.W.Cont.continuous_at_place
    PI.LevelKSplit.W.Meas.lattice_borel

theorem levelSAll_of_exist (h1 : PI.LevelKSplit.W.ExistSAll) : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Split.levelSAll_of_existS_measKf h1 maximal_compact_measurable

end PI.LevelKSplit.W.MeasAll
