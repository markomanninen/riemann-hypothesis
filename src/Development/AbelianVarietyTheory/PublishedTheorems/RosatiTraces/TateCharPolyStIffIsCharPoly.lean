module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def TateCharPolySt : Prop := EndCharPolySt

end GlobalTheory.Published

namespace GlobalTheory.TateCharPoly

open ThetaDetCompare ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)}

variable [IsAlgClosed K]

end GlobalTheory.TateCharPoly
