module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_conjugation_compat_complex_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E),
    ComplexEmbedding.conjugate τ (a : E) = τ (H.bar a : 𝓞 E) ∧ H.bar (H.bar a) = a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.conjugate_coe_eq_bar <;> assumption)
