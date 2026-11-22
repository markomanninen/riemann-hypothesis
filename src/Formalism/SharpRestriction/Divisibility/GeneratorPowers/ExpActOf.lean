module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf

@[expose] public section

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expActOf_of (hE : LinEigSt) : ExpActOfSt := expActOf_of_eig hE

end Formalism.MainNotions.ModuliIntegralCharts.H1
