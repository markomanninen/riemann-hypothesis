module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_comp_of_isOpenImmersion_surjective : ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  first | exact @GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | exact GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective | (intros; apply GlobalTheory.geometricallyIntegral_of_isOpenImmersion_comp_surjective <;> assumption)
