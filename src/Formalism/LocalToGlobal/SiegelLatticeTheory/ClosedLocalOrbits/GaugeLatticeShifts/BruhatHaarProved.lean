module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacGaugeOfSandwichRhsWLim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstSandwich

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_rhsW (hL : WB.RhsWLim) : JacGauge := jacGauge_of_sandwich_rhsWLim BH.sandwich' hL

end Formalism.L2.SG.Pf
