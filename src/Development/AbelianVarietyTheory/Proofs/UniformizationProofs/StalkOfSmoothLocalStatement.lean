module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_regular_flat_of_smooth : ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → IsNoetherianRing (X.presheaf.stalk x) ∧ σ.Flat ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) ∧ ringKrullDim (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) = g := by
  first | exact @GlobalTheory.StabFlat.stalk_of_smooth_local | exact GlobalTheory.StabFlat.stalk_of_smooth_local | (intros; apply GlobalTheory.StabFlat.stalk_of_smooth_local <;> assumption)
