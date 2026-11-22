module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicCoordSimilitudeThetaProduct
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_coord_similitudeThetaProduct : ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∀ k n : Fin 4 → Fin g → ℤ, ∃ qa : (Fin g → Fin g → ℂ) → (Fin 4 → Fin (m ^ g)) → ℂ, (∀ I, DifferentiableOn ℂ (fun p => qa p I) (Key.phDom g)) ∧ ∀ p ∈ Key.phDom g, ∀ q : (Fin 4 → Fin (m ^ g)) → ℂ, (∀ y, simTheta (per p) a b al m k n y = ∑ I, q I * ∏ c, Th (I c) p (y c)) ↔ q = qa p := by
  first | exact @GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | exact GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | (intros; apply GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta <;> assumption)
