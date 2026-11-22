module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_mulEquiv_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

end GlobalTheory.GroupBplus.Aff
