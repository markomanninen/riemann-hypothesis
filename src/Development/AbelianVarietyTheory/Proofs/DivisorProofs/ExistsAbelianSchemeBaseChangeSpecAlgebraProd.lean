module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
theorem exists_baseChange_spAlg_prod (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) [GrpObj B] (g : ℕ) :
    IsAbelianScheme B → SmoothOfRelativeDimension g B.hom →
      ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left)
        (q : B'.left ⟶ (SpAlg R D ⊗ B).left),
        IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧
          SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧
          q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  intro hA hg
  let f := spMap (algebraMap R D)
  refine ⟨(Over.pullback f).obj B, inferInstance, Limits.pullback.fst B.hom f,
    (Limits.pullbackSymmetry B.hom f).hom,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B f,
    GlobalTheory.isAbelianScheme_pullback_obj f B hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback B.hom f) hg,
    inferInstance, Limits.pullbackSymmetry_hom_comp_fst B.hom f,
    Limits.pullbackSymmetry_hom_comp_snd B.hom f⟩

end GlobalTheory
