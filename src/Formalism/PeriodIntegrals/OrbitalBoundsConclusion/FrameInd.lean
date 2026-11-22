module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FrameInductionOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.QBuild
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose

@[expose] public section

theorem frameInd : Formalism.FourierDecayAlt.C2.GramIndependentSignature :=
  PI.FrameInd.frame_induction_of PI.FrameInd.signStep (PI.FrameInd.UPosW.uPos_of PI.FrameInd.negative_bound)
