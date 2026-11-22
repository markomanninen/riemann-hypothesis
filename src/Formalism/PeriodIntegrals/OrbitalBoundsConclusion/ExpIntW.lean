module

public import Formalism.PeriodIntegrals.ExpIntW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.RootsOfUnityRingLeWittIntegers

@[expose] public section

theorem expIntegralWitt : PI.ExpIntW :=
  PI.ExpIntWProof.expIntW_of_key PI.ExpIntWProof.stepI PI.ExpIntWProof.keyW
