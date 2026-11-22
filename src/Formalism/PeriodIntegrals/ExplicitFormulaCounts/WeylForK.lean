module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForU

@[expose] public section

theorem weylForK_closed : PI.WeylForK := weylForK_of weylForU_closed
