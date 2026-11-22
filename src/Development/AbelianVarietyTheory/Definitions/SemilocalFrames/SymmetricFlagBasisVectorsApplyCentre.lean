module

public import Mathlib
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram

@[expose] public section

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

def xPlus (F : FlagD H r) : Submodule K V := F.X ⊔ Submodule.span K {F.z}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def IsComp (F F' : FlagD H r) (u : V) (a a' : K) : Prop := u - a • F.z - a' • F'.z ∈ F.X ⊔ F'.X

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ

def fixSp (F F' F'' : FlagD H r) (β : V ≃ₗ[K] V) : Submodule K V where
  carrier := {x | x ∈ wSp F F' ∧ ∃ x'' ∈ wSp F F'', x - x'' ∈ F.X ∧ β x - x'' ∈ F''.X}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, a, ha, h1, h2⟩ ⟨hy, b, hb, h3, h4⟩
    refine ⟨add_mem hx hy, a + b, add_mem ha hb, ?_, ?_⟩
    · rw [add_sub_add_comm]; exact add_mem h1 h3
    · rw [map_add (f := _), add_sub_add_comm]; exact add_mem h2 h4
  smul_mem' := by
    rintro c x ⟨hx, a, ha, h1, h2⟩
    refine ⟨Submodule.smul_mem _ c hx, c • a, Submodule.smul_mem _ c ha, ?_, ?_⟩
    · rw [← smul_sub]; exact Submodule.smul_mem _ c h1
    · rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ c h2

theorem perp_anti {S S' : Submodule K V} (h : S ≤ S') : perp H S' ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H S' y).1 hy x (h hx)

theorem perp_sup (S S' : Submodule K V) : perp H (S ⊔ S') = perp H S ⊓ perp H S' := by
  refine le_antisymm (le_inf (perp_anti le_sup_left) (perp_anti le_sup_right)) fun y hy => ?_
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), (mem_perp_iff H _ y).1 hy.1 a ha, (mem_perp_iff H _ y).1 hy.2 b hb, add_zero]

theorem mem_perp_span (s : Set V) (y : V) :
    y ∈ perp H (Submodule.span K s) ↔ ∀ x ∈ s, H.B y x = 0 := by
  rw [mem_perp_iff]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, ha, smul_zero]

theorem X_eq_span (F : FlagD H r) :
    F.X = Submodule.span K (Set.range fun a : Fin r => F.e a.castSucc) := by
  rw [FlagD.X, FlagD.Xa, ← Set.image_univ]
  congr 2
  ext b
  simp

theorem xPlus_eq_span (F : FlagD H r) : xPlus F = Submodule.span K (Set.range F.e) := by
  rw [xPlus, X_eq_span, ← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Fin.exists_fin_succ', FlagD.z, eq_comm]

theorem mem_perp_xPlus (F : FlagD H r) (y : V) :
    y ∈ perp H (xPlus F) ↔ y ∈ perp H F.X ∧ H.B y F.z = 0 := by
  rw [xPlus, perp_sup, Submodule.mem_inf, mem_perp_span]
  simp



theorem xPlus_sup (F F' : FlagD H r) : xPlus F ⊔ xPlus F' = V0 F F' := by
  rw [xPlus, xPlus, V0, Submodule.span_insert, sup_sup_sup_comm]

theorem wSp_eq (F F' : FlagD H r) : wSp F F' = perp H (xPlus F) ⊓ perp H (xPlus F') := by
  rw [wSp, ← xPlus_sup, perp_sup]

section Pair

variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

end Pair

namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

end FlagExample

end GlobalTheory.SA

end
