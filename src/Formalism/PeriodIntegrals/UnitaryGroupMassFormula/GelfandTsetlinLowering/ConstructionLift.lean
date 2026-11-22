module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvDiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvWt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.NablaSqLeOfGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTuple
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftAsm

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem liftMod_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hZ : CapelliZ) (hV : ZScalarVanish)
    (hN : Numbers) (hX : XiFacts) : LiftMod :=
  liftMod_asm hZ hV hN hX equivariant_divisibility equivariant_partial_weight (decomp_of h4 equivariant_last_degree)
    (zComm_of h4 equivariant_divisibility equivariant_partial_weight) (fockDetect_of h3 equivariant_divisibility) tuple_decomposition_formula

end PI.WGL
