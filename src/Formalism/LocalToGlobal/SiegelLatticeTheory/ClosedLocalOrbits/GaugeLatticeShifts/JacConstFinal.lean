module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

theorem WB.rhsWLim' [Fact Formalism.L2.SG.Pf.WB.RhsWLim] : WB.RhsWLim := Fact.out


variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem jacGauge : JacGauge := jacGauge_of_rhsW WB.rhsWLim'

end Formalism.L2.SG.Pf
