module

public import Mathlib
public import Formalism.PeriodIntegrals.SqPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.FiniteAdeleIdempotentOfFMulSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.HyperbolicPlane
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairDichotomy
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PairSelection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.CmpSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.StepGlue

@[expose] public section

theorem local_cartan_pair : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
