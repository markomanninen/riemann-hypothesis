module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryComm
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := by
  first | exact @GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | exact GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | (intros; apply GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm <;> assumption)
