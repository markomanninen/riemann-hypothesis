module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  first | exact @GlobalTheory.ZM.projRep_projective_ample | exact GlobalTheory.ZM.projRep_projective_ample | (intros; apply GlobalTheory.ZM.projRep_projective_ample <;> assumption)
