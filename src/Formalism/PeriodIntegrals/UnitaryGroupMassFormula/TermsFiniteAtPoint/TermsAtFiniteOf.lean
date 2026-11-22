module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Development

@[expose] public section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigOK_holds (D : D7) : (VS D).SigOK := D.sp.Y_sig 0

end PI.TermsAtPtFiniteW
