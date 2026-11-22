module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
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
theorem _root_.GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal : ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  first | exact @GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | exact GlobalTheory.flat_of_isFinite_of_flat_localization_maximal | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_localization_maximal <;> assumption)
