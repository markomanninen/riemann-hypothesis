module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
open GlobalTheory.FockAlg (genSub)

noncomputable section

namespace GlobalTheory.CommonQuot

variable {p q : ℕ}

section General

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub' (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v - ((μ a : ℚ) : ℂ) • v = 0) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

theorem isKC_diag' (a : Ix p q) : IsKC (Eab a a) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> simp [sameBlock] at h

theorem isKC_pos' {a b : Ix p q} (hab : posC a b) : IsKC (Eab a b) := by
  intro c d h
  rw [Eab, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem map_hw {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub a μ) : g v ∈ hwSub b μ := by
  rw [mem_hwSub'] at hv ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hg, ← map_smul, ← map_sub, hv.1 c, map_zero]
  · rw [← hg, hv.2 c d h, map_zero]

theorem map_wts {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ V'}
    (g : V →ₗ[ℂ] V') (hg : ∀ Z v, g (a Z v) = b Z (g v)) {x : V}
    (hx : x ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ) : g x ∈ ⨆ μ : Ix p q → ℚ, wtSub b μ := by
  refine Submodule.iSup_induction _ (motive := fun v => g v ∈ _) hx ?_ (by simp) ?_
  · intro μ y hy
    refine Submodule.mem_iSup_of_mem μ ?_
    simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
    intro c
    rw [← hg, ← map_smul, ← map_sub, hy c, map_zero]
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

end General

section Constructions

end Constructions

section Max

end Max

section Main

end Main

end GlobalTheory.CommonQuot
