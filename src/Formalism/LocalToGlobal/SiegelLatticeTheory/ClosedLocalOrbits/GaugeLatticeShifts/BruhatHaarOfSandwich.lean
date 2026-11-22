module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolLim

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.GE

theorem jacGauge_of_hearts3 (hS : Sandwich) (hU : ExistsGaugeMeasureForEachRank) (hL : RhsWLim) : JacGauge :=
  jacGauge_of_sandwich_gaugeMeasure hS VL.volLim hU hL

end Formalism.L2.SG.Pf
