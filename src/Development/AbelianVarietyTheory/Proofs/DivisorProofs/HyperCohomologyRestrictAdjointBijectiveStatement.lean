module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) → Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.AdjHyp.main | exact GlobalTheory.AdjHyp.main | (intros; apply GlobalTheory.AdjHyp.main <;> assumption)
