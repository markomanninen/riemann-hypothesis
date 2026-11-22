module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  first | exact @GlobalTheory.Obs.unobDim_of_formSt | exact GlobalTheory.Obs.unobDim_of_formSt | (intros; apply GlobalTheory.Obs.unobDim_of_formSt <;> assumption)
