module

public import Mathlib
public import Formalism.PeriodIntegrals.ExplicitFormula
public import Formalism.PeriodIntegrals.ZerosWindow
public import Formalism.PeriodIntegrals.ZerosWindowIn
public import Formalism.PeriodIntegrals.DiscIn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers

@[expose] public section

theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
