module

public import Formalism.PeriodIntegrals.StdCharTR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardCharacterTrace.SumEmbeddingEqTrace

@[expose] public section

theorem stdCharTR : PI.StdCharTR.Target :=
  PI.StdCharTRWork.stdCharTR_main
