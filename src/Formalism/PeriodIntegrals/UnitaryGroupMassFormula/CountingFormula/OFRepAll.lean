module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepRank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Stage1OfUnipotentIntegralIsGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TransMemUnipotentIntegral

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem orbit_count_first_stage : Stage1 := stage1_of_unipotentIntegralIsGroup unipotent_integral_isGroup

theorem orbitReps_of_stage2 (h2 : Stage2) : OrbitReps :=
  orbitReps_of unipotent_integral_isGroup rank_gram good_places_integral orbit_count_first_stage h2 finite_level_index

end PI.UnitaryGroupMassFormula.CntFormula
