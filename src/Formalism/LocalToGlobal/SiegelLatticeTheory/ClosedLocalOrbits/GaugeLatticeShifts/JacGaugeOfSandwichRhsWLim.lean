module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarOfSandwich
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsGaugeNormalizedStabilizer

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_sandwich_rhsWLim (hS : BH.Sandwich) (hL : WB.RhsWLim) : JacGauge :=
  jacGauge_of_hearts3 hS GE.existsGaugeNormalizedStabilizer hL

end Formalism.L2.SG.Pf
