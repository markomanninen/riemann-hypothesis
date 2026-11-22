module

public import Mathlib
public import Formalism.PeriodIntegrals.DCRelEquiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
