module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

def GeneratesFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  ∀ x : F, ∃ r s : O, β s ≠ 0 ∧ x * β s = β r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def UnivCompat {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂) {S : Scheme.{0}} {t : SAB H S} {χ₁ : S ⟶ Y₁.X} {χ₂ : S ⟶ Y₂.X}
    (m₁ : SABMap t Y₁.t χ₁) (m₂ : SABMap t Y₂.t χ₂) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y₁.oF.t.G.left) (g₂ : T ⟶ Y₂.oF.t.G.left),
    g ≫ m₁.φ = g₁ ≫ Y₁.m.φ → g₁ ≫ Y₁.m0.toSABMap.φ = g₂ ≫ Y₂.m0.toSABMap.φ →
    g₁ ≫ Y₁.oF.t.G.hom = g₂ ≫ Y₂.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y₂.m.φ

def SameWitness {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂) : Prop :=
  ∃ (m₂ : SABMap W₁.t Y₂.t χ₂) (h : _),
    W₂ = { t := W₁.t, m := m₂, P := W₁.P, φ := W₁.φ, he := W₁.he, w := W₁.w, e := W₁.e, spec := h } ∧
    UnivCompat Y₁ Y₂ W₁.m m₂

end GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs
