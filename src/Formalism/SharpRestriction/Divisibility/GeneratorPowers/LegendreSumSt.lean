module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPolynomial Formalism.L2.Pj

section Crude

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ)

end Crude

section Germ

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

end Germ

end Formalism.MainNotions.ModuliIntegralCharts.H1
