module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AprimeInfOfLeaves

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

end PI.AprimeInfW
