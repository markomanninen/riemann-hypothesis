module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarizedFamilyOfThetaUniformization
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_family_of_theta_uniformization : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → PolFam := by
  first | exact @GlobalTheory.KeyFam.polFam | exact GlobalTheory.KeyFam.polFam | (intros; apply GlobalTheory.KeyFam.polFam <;> assumption)
