module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

@[expose] public section

namespace PI.VolStabSW.TopoAF

theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
