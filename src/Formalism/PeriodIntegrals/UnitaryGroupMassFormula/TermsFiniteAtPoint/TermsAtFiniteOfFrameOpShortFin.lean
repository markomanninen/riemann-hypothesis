module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FixedZ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatRed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatIntegralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.RightInvHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolveAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DdSPowLeOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFinAlt

@[expose] public section

noncomputable section

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termsAtFinite_of_frameOp_shortFin (hF : FrameOp) (hS : ShortFin) (D : D7) (u u' : D.what₂.Word) :
    TermsAtFinite D u u' :=
  termsAtFinite_of (zhatReduce_of cellReduce_holds hF carrierRow_holds zhatIntegral_holds)
    (fixedZhat_of heisOp_holds skewSolve_holds hS rowsDep_holds rightInv_holds fInt_holds resFin_holds) D u u'

end PI.TermsAtPtFiniteW
