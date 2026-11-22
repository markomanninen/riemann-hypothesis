module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap

@[expose] public section

open scoped TensorProduct
universe u

namespace GlobalTheory.HTRho

theorem mSub_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ x
  let : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _) with hφdef
  have hsmul : ∀ (a : k ⊗[ℤ] C) (y : H), a • y = L a y := fun _ _ => rfl
  have hLt : ∀ (l : k) (c : C) (y : H), L (l ⊗ₜ c) y = l • σ c y := by
    intro l c y
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H))
        σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) l c)
  have hφt : ∀ (l : k) (c : C), φ (l ⊗ₜ c) = l * χ c := by
    intro l c
    simp [hφdef, Algebra.TensorProduct.lift_tmul]
  have key : ∀ (a : k ⊗[ℤ] C) (y : H), L a y - φ a • y ∈ mSub σ χ ⊤ := by
    intro a y
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hLt, hφt, mul_smul, ← smul_sub]
      refine Submodule.smul_mem _ l (Submodule.subset_span ⟨c, y, trivial, ?_⟩)
      simp
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      have hmem : ((1 : k) ⊗ₜ c - (χ c) ⊗ₜ (1 : C)) ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker]
        simp [hφt]
      have := Submodule.smul_mem_smul hmem (Submodule.mem_top (x := y))
      convert this using 1
      rw [hsmul, map_sub, LinearMap.sub_apply, hLt, hLt]
      simp
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul l z _ hz =>
      have : l • z = ((l ⊗ₜ (1 : C) : k ⊗[ℤ] C)) • z := by
        rw [hsmul, hLt]; simp
      rw [this]
      exact Submodule.smul_mem _ _ hz
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun a b ha hb => add_mem ha hb)
    rw [hsmul]
    have := key a y
    rwa [(RingHom.mem_ker).1 ha, zero_smul, sub_zero] at this

end GlobalTheory.HTRho
