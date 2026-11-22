module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceJacHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NormSqDetOfUnitary

@[expose] public section

namespace PI.AprimeInfW

theorem placeJacAll_holds : PlaceJacAll := placeJacAll_of placeJac_holds

end PI.AprimeInfW
