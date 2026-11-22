module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
public import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

@[expose] public section

noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

end GlobalTheory.WeightTwoHeckePower
