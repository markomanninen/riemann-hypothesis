module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianScheme
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLieSequence_exact_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LieExact A := by
  first | exact @GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham | exact GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham | (intros; apply GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham <;> assumption)
