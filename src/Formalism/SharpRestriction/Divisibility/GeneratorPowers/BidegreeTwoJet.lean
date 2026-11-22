module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace BidegreeTwoJet

section Jets

variable {V : Type} [CommRing V] {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] {n d : ℕ}

def zV (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) : jOG (𝟙 (Sp V)) d m n ⟶ G' :=
  pG.lim.lift (Fan.mk _ fun i => homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m)

end Jets

section Coord

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D' : DegData V I}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' G : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  {n d : ℕ}

end Coord


end BidegreeTwoJet
end Formalism.MainNotions.ModuliIntegralCharts.H1
