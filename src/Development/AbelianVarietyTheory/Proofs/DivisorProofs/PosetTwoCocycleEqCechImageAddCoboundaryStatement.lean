module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundary
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
theorem _root_.GlobalTheory.T.exists_cocycle_sub_e2_eq_d1 : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := by
  first | exact @GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | exact GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary | (intros; apply GlobalTheory.CechPoset.posetTwoCocycle_eq_cechImage_add_coboundary <;> assumption)
