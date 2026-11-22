module

public import Formalism.PeriodIntegrals.ScPiExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.InnerOfNorm

@[expose] public section

theorem sc_pi_construction : PI.ScPiExists.Build :=
  PI.ScPiBuildW.Asm.build
