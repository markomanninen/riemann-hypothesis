module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaGeneratorPullbackMulConstInFrames
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
theorem _root_.GlobalTheory.T.theta_generator_pullback_mul_const_in_frames : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = C * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := by
  first | exact @GlobalTheory.SimilTheta.generator_mul_const_in_frames | exact GlobalTheory.SimilTheta.generator_mul_const_in_frames | (intros; apply GlobalTheory.SimilTheta.generator_mul_const_in_frames <;> assumption)
