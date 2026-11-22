module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelFrobGrp

open GlobalTheory.AbDual GlobalTheory.PDiv

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem main : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  intro p _ R _ hR A A₁ _ _ π hπ
  have mF : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR)
      (spMap (frobR p R hR)) (GlobalTheory.VB.frob A.left p (cast_left p R hR A)) := by
    refine ⟨isDPMorphism_of_eq_bot _ rfl _ _, ?_, frob_comp_hom p R hR A.hom _, ?_⟩
    · simp
    · intro T x y x₀ y₀ hx hy
      have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
      have hn (f : T.left ⟶ A.left) :
          GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p (cast_left p R hR A) :=
        GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT _
      let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
        Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
      have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
        simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
      have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
        simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
      subst ex ey
      rw [← MonObj.comp_mul]
      simp only [Over.comp_left, Over.homMk_left, j]
      exact hn (x * y).left
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  refine ⟨F, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, hF⟩
  have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
  exact congrArg (fun z ↦ z.left) e

end GlobalTheory.RelFrobGrp
