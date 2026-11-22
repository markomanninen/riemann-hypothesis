module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap

@[expose] public section

open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom;
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  let φ := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _)
  let : Module (k ⊗[ℤ] C) H := Module.compHom H L.toRingHom
  let X := GlobalTheory.HTRho.mSub σ χ ⊤
  let Y : Submodule (k ⊗[ℤ] C) H := RingHom.ker φ • ⊤
  change ∀ x : H, x ∈ X ↔ x ∈ Y
  have hsmul (a : k ⊗[ℤ] C) (y : H) : a • y = L a y := rfl
  have hL (l : k) (c : C) (y : H) : L (l ⊗ₜ c) y = l • σ c y := by
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
        (fun _ _ => Algebra.commutes _ _) l c)
  have hφ (l : k) (c : C) : φ (l ⊗ₜ c) = l * χ c := by
    simp [φ]
  have hSub (a : k ⊗[ℤ] C) (y : H) : L a y - φ a • y ∈ X := by
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hL, hφ, mul_smul, ← smul_sub]
      exact Submodule.smul_mem X l (Submodule.subset_span ⟨c, y, trivial, by simp⟩)
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      let a : k ⊗[ℤ] C := 1 ⊗ₜ c - χ c ⊗ₜ (1 : C)
      have ha : a ∈ RingHom.ker φ := by
        change φ a = 0
        simp [a, hφ]
      have hy : a • y ∈ Y := Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
      have hay : a • y = σ (algebraMap C C c) y - χ c • y := by
        rw [hsmul]
        simp [a, hL]
      exact hay ▸ hy
    | zero => exact Y.zero_mem
    | add a b _ _ ha hb => exact Y.add_mem ha hb
    | smul l z _ hz =>
      have hl : (l ⊗ₜ (1 : C) : k ⊗[ℤ] C) • z = l • z := by
        rw [hsmul, hL, map_one, one_apply_eq_self]
      exact hl ▸ Y.smul_mem _ hz
  · intro hx
    refine Submodule.smul_induction_on (show x ∈ RingHom.ker φ • ⊤ from hx) ?_ ?_
    · intro a ha y _
      rw [hsmul]
      simpa only [RingHom.mem_ker.mp ha, zero_smul, sub_zero] using hSub a y
    · intro a b ha hb
      exact X.add_mem ha hb
