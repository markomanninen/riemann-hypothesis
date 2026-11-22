module

public import Mathlib

@[expose] public section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Ord

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def ordPart (U : Module.End R M) : Submodule R M := ⨅ n : ℕ, LinearMap.range (U ^ n)

theorem mem_ordPart {U : Module.End R M} {x : M} : x ∈ ordPart U ↔ ∀ n : ℕ, ∃ y, (U ^ n) y = x := by
  simp [ordPart, Submodule.mem_iInf]

theorem map_mem_smul_top {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (J : Ideal R)
    {x : M} (hx : x ∈ (J • ⊤ : Submodule R M)) : f x ∈ (J • ⊤ : Submodule R N) := by
  have h1 := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

def nilPart (I : Ideal R) (U : Module.End R M) : Submodule R M where
  carrier := {x | ∀ k : ℕ, ∃ n : ℕ, (U ^ n) x ∈ (I ^ k • ⊤ : Submodule R M)}
  zero_mem' := fun k => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨n, hn⟩ := hx k
    obtain ⟨m, hm⟩ := hy k
    refine ⟨n + m, ?_⟩
    rw [map_add (f := _)]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hn
    · rw [pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hm
  smul_mem' := by
    intro c x hx k
    obtain ⟨n, hn⟩ := hx k
    exact ⟨n, by rw [map_smul]; exact Submodule.smul_mem _ _ hn⟩

structure IsOrdProj (I : Ideal R) (U e : Module.End R M) : Prop where
  idem : IsIdempotentElem e
  comm : Commute U e
  bij : Set.BijOn U (LinearMap.range e) (LinearMap.range e)
  nil : ∀ k : ℕ, ∃ n : ℕ, ∀ x, (U ^ n) (x - e x) ∈ (I ^ k • ⊤ : Submodule R M)

def IsFactLim (I : Ideal R) (U e : Module.End R M) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ x, (U ^ j.factorial) x - e x ∈ (I ^ k • ⊤ : Submodule R M)


open Classical in
noncomputable def ordProj (I : Ideal R) (U : Module.End R M) : Module.End R M :=
  by
    classical
    exact if h : ∃ e, IsOrdProj I U e then h.choose else 0

theorem isOrdProj_ordProj {I : Ideal R} {U : Module.End R M} (h : ∃ e, IsOrdProj I U e) :
    IsOrdProj I U (ordProj I U) := by
  unfold ordProj
  rw [dite_eq_left h]
  exact h.choose_spec


variable (M) in
structure OrdAdm (I : Ideal R) : Prop where
  complete : IsAdicComplete I M
  finLen : ∀ k : ℕ, IsFiniteLength R (M ⧸ (I ^ k • ⊤ : Submodule R M))

end Ord

section Map

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
  {M : Type*} [AddCommGroup M] [Module A M]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

theorem pow_intertwine {U : Module.End A M} {U' : Module.End A' M'} {f : M →ₗ[A] M'}
    (h : ∀ x, f (U x) = U' (f x)) (n : ℕ) (x : M) : f ((U ^ n) x) = (U' ^ n) (f x) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

end Map

section Lim

variable {R : Type*} [CommRing R] {P : ℕ → Type*} [∀ b, AddCommGroup (P b)] [∀ b, Module R (P b)]
  {Q : ℕ → Type*} [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)]

end Lim

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
