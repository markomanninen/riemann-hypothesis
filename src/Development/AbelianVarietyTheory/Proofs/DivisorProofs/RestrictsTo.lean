module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

variable {α β α' β' r}

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := End.of (biprod.map (act α x) (act β x))
  map_one' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_mul' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act, Category.assoc]
  map_zero' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_add' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Dieu

end GlobalTheory.TwoSeq
