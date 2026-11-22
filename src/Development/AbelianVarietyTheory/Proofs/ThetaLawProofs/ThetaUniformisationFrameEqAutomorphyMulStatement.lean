module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMul
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
theorem _root_.GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  first | exact @GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | exact GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | (intros; apply GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul <;> assumption)
