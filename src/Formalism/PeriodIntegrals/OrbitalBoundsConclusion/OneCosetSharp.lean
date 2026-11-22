module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.OneCosetSharpOfPatClosed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZeroAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.AllowColLt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix

@[expose] public section

theorem support_oneCoset : PI.OneCosetSharp.OneCosetSharp :=
  PI.OneCosetSharp.W.oneCosetSharp_of_patClosed PI.OneCosetSharp.W.patClosed PI.OneCosetSharp.W.kappaZero
    PI.OneCosetSharp.W.nElem PI.OneCosetSharp.W.gaStep PI.OneCosetSharp.W.C2.claim2
