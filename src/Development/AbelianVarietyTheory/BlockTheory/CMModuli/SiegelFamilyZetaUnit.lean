module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Triple

variable {S : Scheme.{0}}

def IsTrivial {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen

def diagPull (A : Over S) (P : LB (A ⊗ A).left) : LB A.left := P.pull (lift (𝟙 A) (𝟙 A)).left

def IsSymmetricPair (h : ℕ) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension h A.hom ∧ P.IsLB ∧
    IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) ∧
    IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) ∧
    LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def slice (A : Over S) (P : LB (A ⊗ A).left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  P.pull (lift (fst T A ≫ x) (snd T A)).left

def IsPrincipal (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  Out.RelAmple A (diagPull A P) ∧ ∀ (T : Over S) (x : T ⟶ A), IsTrivial (slice A P x) → x = 1

abbrev Std (h M : ℕ) : Type := (Fin h → ZMod M) × (Fin h → ZMod M)

def stdForm {h M : ℕ} (a b : Std h M) : ZMod M := ∑ i, (a.1 i * b.2 i - a.2 i * b.1 i)

def IsLevel {h M : ℕ} (A : Over S) [GrpObj A] (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lv (a + b) = lv a * lv b) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g

def IsSymplectic {h M : ℕ} {R : Type} [CommRing R] (ζ : Rˣ) (s : S ⟶ Sp R) (A : Over S) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ a b, Out.WeilIs A (diagPull A P) (M : ℤ) (lv a) (lv b)
    (Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val)))

def IsPullbackTriple {h M : ℕ} {S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lv' : Std h M → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧
    φ₂ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ φ₂ ≫ (snd A A).left = (snd A' A').left ≫ φ ∧
    LBIso P' (P.pull φ₂) ∧
    ∀ a, (lv' a).left ≫ φ = f ≫ (lv a).left

end Triple

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
