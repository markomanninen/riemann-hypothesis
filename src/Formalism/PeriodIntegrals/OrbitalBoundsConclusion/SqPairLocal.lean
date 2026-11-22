module

public import Mathlib
public import Formalism.PeriodIntegrals.SqPair
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocCartanPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOf

@[expose] public section

theorem square_pair_local : PI.SqPair.PLocalAll := PI.SqPairLocal.sqPairLocal_of local_cartan_pair
