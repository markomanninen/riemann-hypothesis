module

public import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

end ChG


section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
