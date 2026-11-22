module

public import Mathlib
public import Formalism.PeriodIntegrals.FockRBlock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.OkSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FilterConcatWLength
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.MultidegSingle
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.NotMemVarsEmbS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.StepMonoFactor

@[expose] public section

theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
