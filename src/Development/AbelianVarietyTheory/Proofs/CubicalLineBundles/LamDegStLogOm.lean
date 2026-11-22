module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieLineDegreeOfEigenLineDegreeFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisationStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvrStatement
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

theorem GlobalTheory.LamF.lamDegSt_logOm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re :=
  fun hΘ hL =>
    GlobalTheory.T.cmLieLineDegree_of_eigenLineDegreeFormula
      (GlobalTheory.T.cmEigenLine_degreeFormula (GlobalTheory.T.cmEllipticCurve_exists_of_uniformisation hΘ hL.polBaseChange GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr) hΘ hL GlobalTheory.T.semiAbelian_hom_extends_uniquely_over_dvr) hΘ hL
