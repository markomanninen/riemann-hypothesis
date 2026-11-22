module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitCountSecondStage

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_representatives : OrbitReps := orbitReps_of_stage2 orbit_count_second_stage

end PI.UnitaryGroupMassFormula.CntFormula
