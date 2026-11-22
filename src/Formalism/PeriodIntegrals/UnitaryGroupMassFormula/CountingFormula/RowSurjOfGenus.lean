module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeUnimodular
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentCoprimeSplit

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem rowSurj_of_genus (hJ : UnimodOneGenus) : RowSurj :=
  rowSurj_of hJ partner_vector_exists lattice_integral lamUnimod lattice_flag_exists local_genus_exists

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
