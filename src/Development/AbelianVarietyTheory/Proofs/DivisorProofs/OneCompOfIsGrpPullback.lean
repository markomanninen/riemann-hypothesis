module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.PPAS

variable {S S' : Scheme.{0}}

theorem one_comp_of_isGrpPullback {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) :
    (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h A'))
  let g : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have e2 : g ≫ (1 : A ⟶ A) = 1 := by simp
  have e3 := congrArg (fun z : Over.mk (A'.hom ≫ f) ⟶ A => z.left) e2
  simp only [Over.comp_left] at e3
  rw [← e3] at e
  exact e

end GlobalTheory.PPAS
