module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedge
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  first | exact @GlobalTheory.AbCoh.dOne_glob_eq_wsum | exact GlobalTheory.AbCoh.dOne_glob_eq_wsum | (intros; apply GlobalTheory.AbCoh.dOne_glob_eq_wsum <;> assumption)
