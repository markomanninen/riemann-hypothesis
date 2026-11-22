module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds

@[expose] public section

namespace PI.VolStabS

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabS
