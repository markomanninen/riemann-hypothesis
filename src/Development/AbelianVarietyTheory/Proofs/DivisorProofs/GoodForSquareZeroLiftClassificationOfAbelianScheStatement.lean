module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodForSquareZeroLiftClassificationOfAbelianSche
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Good A.hom := by
  first | exact @GlobalTheory.LiftSys.good_of_isAbelianScheme | exact GlobalTheory.LiftSys.good_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.good_of_isAbelianScheme <;> assumption)
