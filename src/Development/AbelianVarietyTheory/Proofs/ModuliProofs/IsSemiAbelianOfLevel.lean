module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Weights
variable {S A Y₁ Y₂ : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A}

end Weights

section Packages
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

variable {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
  {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

end Packages

section Triv
variable {S S' : Scheme.{0}} {G : Over S} {G' H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  [GrpObj H] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G'}

variable {S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_even_of_desc {Q : TQ G X} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have := Q.i_hom
  obtain ⟨s, hs, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left])
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v' : ∀ (Z : Scheme.{0}) r (z : Z) J, Good D.M.L.L z J → val s r z J = 1 := fun Z r z J hJ =>
    (v Z r z J hJ).trans (val_one _)
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  refine TowerEx.exists_even_pull D.map (e ▸ TorusCompat.of_comp Q.i Q.q : TorusCompat _ _ Q.i 1)
    ⟨s, hs, fun T x y u z J hJ => ?_⟩ fun T x z J hJ => ?_
  · simp only [v' _ _ z J hJ, MonObj.comp_one, _root_.mul_one]
    exact ((isCub_cubV D.M.c (T := T) hJ).face 1 1).symm
  · show val s _ z J = _ * val s _ z J
    rw [v' _ _ z J hJ, v' _ _ z J hJ, MonObj.comp_one, D.M.val_sym_one hJ, _root_.mul_one]

end Triv

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    (Q' : TQ G' X) : ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i := by
  obtain ⟨Q, hQ, -⟩ := TowerEx.exists_lift hA φ hφ G G' hF (P := CP.triv G) (P' := CP.triv G')
    (IsCPMap.triv (hw := hF.1.w) (TowerEx.toBase_mul hF _)) Q' ⟨CubTriv.triv _, CubTriv.triv_even _⟩
  exact ⟨Q, hQ⟩

section Levels
variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  [Module.Free ℤ X] [Module.Finite ℤ X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}
  [ConnectedSpace S₁] {L₁ : Level P X f₁ G₁ F₁ h₁} {L₂ : Level P X f₂ G₂ F₂ h₂} {t : S₁ ⟶ S₂} {m : G₁.left ⟶ G₂.left}


variable {B : Over S} [GrpObj B] [IsCommMonObj B] {M : CP B}




end Levels

end GlobalTheory.UniformizationSetting
end
