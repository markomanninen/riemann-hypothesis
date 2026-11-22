module

public import Mathlib
public import Formalism.PeriodIntegrals.PhConvProj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.SelfAdj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.UrepMulApply

@[expose] public section

theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
