module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  first | exact @GlobalTheory.CapelliCoef.capelli_coef | exact GlobalTheory.CapelliCoef.capelli_coef | (intros; apply GlobalTheory.CapelliCoef.capelli_coef <;> assumption)
