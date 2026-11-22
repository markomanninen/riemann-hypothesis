module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwo
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
theorem _root_.GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := by
  first | exact @GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | exact GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero | (intros; apply GlobalTheory.CechPoset.e2_mem_Z2_of_delta_eq_zero <;> assumption)
