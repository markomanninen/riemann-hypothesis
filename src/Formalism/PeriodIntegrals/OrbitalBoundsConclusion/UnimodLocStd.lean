module

public import Mathlib
public import Formalism.PeriodIntegrals.UnimodLocStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsIsometryMemLocalizedAtSingle
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKeyRam
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamAsm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.UnitVecRam

@[expose] public section

theorem unimodular_local_standard : PI.UnimodLocStd :=
  PI.UnitaryGroupMassFormula.UnimodLocStd.target_of_key
    (PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_ram
      (PI.UnitaryGroupMassFormula.UnimodLocStd.keyStartRam_of_unit PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam))
