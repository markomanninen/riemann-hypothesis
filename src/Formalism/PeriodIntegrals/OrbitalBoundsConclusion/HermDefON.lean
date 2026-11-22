module

public import Mathlib
public import Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDefiniteOrthonormal.Imports

@[expose] public section

theorem posDefCongruentOne : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
