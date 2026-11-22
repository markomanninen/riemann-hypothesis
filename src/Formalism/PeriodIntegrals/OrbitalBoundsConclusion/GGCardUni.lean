module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper

@[expose] public section

theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
