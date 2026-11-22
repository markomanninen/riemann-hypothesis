module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

section Group

variable (G : Over X₀) [GrpObj G] [IsCommMonObj G]

variable (x : Sp S ⟶ X₀) {d : ℕ}


variable {G x}

end Group

section Germ

variable {G : Over X₀} [GrpObj G] {x : Sp S ⟶ X₀} {d : ℕ}

end Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev PrimIso (t : SAB H X₀) : Type :=
  LB.Iso t.PP.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] t.PP.L)

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames
