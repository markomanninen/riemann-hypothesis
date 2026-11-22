module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum

theorem over_pullback_map_left_comp_pullbackFst_scheme {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    ((Over.pullback f).map g).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end GlobalTheory.Mum
