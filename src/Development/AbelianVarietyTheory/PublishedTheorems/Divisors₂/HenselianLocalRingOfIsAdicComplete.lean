module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Raynaud

section Formal

variable {R : Type} [CommRing R] (I : Ideal R)

variable {I}

end Formal

section Parts

variable {S : Scheme.{0}}

variable {V : Type} [CommRing V]

theorem pow_eq_one_iff_of_isGrpPullback {S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {Y : Over S'} (y : Y ⟶ G') (n : ℕ) :
    pushPt h.1.w y ^ n = 1 ↔ y ^ n = 1 := by
  let m : (Y ⟶ G') →* (Over.mk (Y.hom ≫ f) ⟶ G) := MonoidHom.mk' (fun z => pushPt h.1.w z) fun a b =>
    Over.OverMorphism.ext (h.2 Y a b _ _ rfl rfl).symm
  have hm : Function.Injective m := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  show m y ^ n = 1 ↔ _
  rw [← map_pow, map_eq_one_iff m hm]

end Parts

end GlobalTheory.Raynaud

namespace GlobalTheory.Published

open GlobalTheory.Raynaud IsLocalRing

end GlobalTheory.Published
