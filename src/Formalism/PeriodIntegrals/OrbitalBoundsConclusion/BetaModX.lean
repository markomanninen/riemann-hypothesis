module

public import Mathlib
public import Formalism.PeriodIntegrals.ScalPairs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.BetaModXOfIota
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds

@[expose] public section

theorem beta_mod_iota_surjective (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaL D u u' :=
  PI.UnitaryGroupMassFormula.BetaModX.betaModX_of_iota PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_surjective_holds D u u'
