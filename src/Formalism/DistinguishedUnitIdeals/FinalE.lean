module

public import Mathlib
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.RhoMapFunctorial
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC

@[expose] public section

namespace Formalism.ExponentWindows.E

theorem theorem_E_assembled : ThmEAssembly :=
  thmE_of rho_map_exists rho_map_linear rho_map_functorial splitting_of_extension

end Formalism.ExponentWindows.E
