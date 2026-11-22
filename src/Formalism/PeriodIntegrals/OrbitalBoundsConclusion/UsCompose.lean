module

public import Mathlib
public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand

@[expose] public section

theorem differential_operator_compose : Formalism.FourierDecayAlt.U.ComposeDD :=
  PI.UnitaryGroupMassFormula.UsCompose.composeDD_of (fun _ X q => PI.UnitaryGroupMassFormula.UsCompose.degDP X q)
    (fun k j ρ => PI.UnitaryGroupMassFormula.UsCompose.degD k j ρ) PI.UnitaryGroupMassFormula.UsCompose.expand
