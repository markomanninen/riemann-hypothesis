module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelevantCarrierNonempty.InSCarrierNonempty

@[expose] public section

theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
