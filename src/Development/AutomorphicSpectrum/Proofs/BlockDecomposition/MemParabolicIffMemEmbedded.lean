module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi


open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in
theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  have mem_iff (m j : ℕ) (g : Mir k (m + j)) :
      g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
        ((g : GL (Fin (m + j + 1)) k) : Matrix _ _ k)
          (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
    show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
    rw [mem_parab_iff]
    constructor
    · intro h b a
      exact h true false b a (by decide)
    · intro h x y i l hxy
      cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l
  rw [mem_iff, mem_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
