module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.UnitsOpenTens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstTestOfPolarWh
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibOrbP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibAllP

@[expose] public section

namespace PI.AprimeInfW

theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
