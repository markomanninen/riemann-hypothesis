module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayValId

@[expose] public section

namespace PI.AprimeInfW

theorem expProdU_holds : ExpProdU := expProdU_of_hua cayDensEx_holds cayValId_holds

end PI.AprimeInfW
