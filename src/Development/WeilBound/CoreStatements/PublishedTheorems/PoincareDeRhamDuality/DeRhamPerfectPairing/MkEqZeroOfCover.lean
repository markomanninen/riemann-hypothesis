module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y : Scheme.{0}}

def pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage y).hom

theorem spMap_pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : spMap (pre y) = y := Spec.map_preimage y

@[reducible] def ptOf (s : X ⟶ Sp R) {B : Type} [CommRing B] (x : Sp B ⟶ X) : Pt s where
  B := B
  alg := (pre (x ≫ s)).toAlgebra
  x := x
  w := (spMap_pre _).symm

variable {s : X ⟶ Sp R}

section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']

end


end CrystallinePoints.Pd
