module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.MirabolicBound

@[expose] public section

theorem mirabolic_bound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
