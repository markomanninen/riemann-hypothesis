module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegActCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Type} [CommRing R] [IsDomain R]

section Act

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Act

section Ext

variable {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] {k : ℕ}

theorem qkExt_unique {f : F →+* F'} {p : QkPt D F k} {q q' : QkPt D F' k} (h : QkExt f p q)
    (h' : QkExt f p q') : q = q' := by
  have hg : q.g = q'.g :=
    TorusExt.gt_ext_val (Over.OverMorphism.ext (h.2.1.trans h'.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (h.2.2 χ) _).trans (val_corr hJ (h'.2.2 χ) _).symm
  have hy : q.y = q'.y := h.1.trans h'.1.symm
  obtain ⟨y, g, e⟩ := q
  obtain ⟨y', g', e'⟩ := q'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

end Ext

section Through

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]

end Through

section Unit

variable (D : DegPre R) (χ : D.X)

end Unit

end GlobalTheory.DegActCompare
