module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbRepOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.KerMeasHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds

@[expose] public section

namespace PI.AprimeInfW

theorem orbRep_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbRep :=
  orbRep_of kerMeas_holds haarUniqInf_holds (regI_of hW) (hinfFin_of hC)

theorem orbUniq_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of (orbRep_of_witt hW hC)

theorem orbUniq_of_compact (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of_witt wittInf_holds hC

end PI.AprimeInfW
