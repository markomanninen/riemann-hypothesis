module

public import Mathlib
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.GradedOscillatorPropertyOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.KroneckerMapOneRightNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit

@[expose] public section

theorem gradedOscillatorProperty : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
